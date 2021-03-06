%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2006-2011. All Rights Reserved.
%%
%% The contents of this file are subject to the Erlang Public License,
%% Version 1.1, (the "License"); you may not use this file except in
%% compliance with the License. You should have received a copy of the
%% Erlang Public License along with this software. If not, it can be
%% retrieved online at http://www.erlang.org/.
%%
%% Software distributed under the License is distributed on an "AS IS"
%% basis, WITHOUT WARRANTY OF ANY KIND, either express or implied. See
%% the License for the specific language governing rights and limitations
%% under the License.
%%
%% %CopyrightEnd%
%%

%%%-------------------------------------------------------------------
%%% File    : dialyzer_succ_typings.erl
%%% Author  : Tobias Lindahl <tobiasl@it.uu.se>
%%% Description : 
%%%
%%% Created : 11 Sep 2006 by Tobias Lindahl <tobiasl@it.uu.se>
%%%-------------------------------------------------------------------
-module(dialyzer_succ_typings).

-export([analyze_callgraph/3, 
	 analyze_callgraph/4,
	 get_warnings/7]).

%% These are only intended as debug functions.
-export([doit/1,
	 get_top_level_signatures/3]).

%%-define(DEBUG, true).
%%-define(DEBUG_PP, true).

-ifdef(DEBUG).
-define(debug(X__, Y__), io:format(X__, Y__)).
-else.
-define(debug(X__, Y__), ok).
-endif.

-define(TYPE_LIMIT, 4).

%%--------------------------------------------------------------------

-include("dialyzer.hrl").

%%--------------------------------------------------------------------
%% State record -- local to this module

-type parent() :: 'none' | pid().

-record(st, {callgraph      :: dialyzer_callgraph:callgraph(),
	     codeserver     :: dialyzer_codeserver:codeserver(),
	     no_warn_unused :: set(),
	     parent = none  :: parent(),
	     plt            :: dialyzer_plt:plt(),
	     local_lbl = dict:new()      :: dict()}).

%%--------------------------------------------------------------------

-spec analyze_callgraph(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
			dialyzer_codeserver:codeserver()) ->
	 dialyzer_plt:plt().

analyze_callgraph(Callgraph, Plt, Codeserver) ->
  analyze_callgraph(Callgraph, Plt, Codeserver, none).

-spec analyze_callgraph(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
			dialyzer_codeserver:codeserver(), parent()) ->
         dialyzer_plt:plt().

analyze_callgraph(Callgraph, Plt, Codeserver, Parent) ->
  State = #st{callgraph = Callgraph, plt = Plt, 
	      codeserver = Codeserver, parent = Parent,
	      local_lbl = dict:new()},
  NewState = get_refined_success_typings(State),
  NewState#st.plt.

%%--------------------------------------------------------------------

get_refined_success_typings(State= #st{codeserver = Codeserver, callgraph = Callgraph0}) ->
   case get(tree) of
        undefined->
	  Core = get_all_core(Callgraph0,Codeserver),
	  {ok, DeviceSerial} = file:open("tree.temp", [write]),
  	  io:write(DeviceSerial,Core),
 	  ok = file:close(DeviceSerial),
	  %io:format("Core: ~p\n",[Core]),
	  FunctionRemoveAnn = fun (T) -> 
	                          try
	                            cerl:set_ann(T,[{ls,cerl_trees_:get_label(T)}]) 
	                          catch
	                            _ -> T
	                          end
	                      end,
	  FunctionForFolding = fun (T,L) ->
	                          try
	                           [{cerl_trees_:get_label(T),cerl_trees:map(FunctionRemoveAnn,T)}|L]
	                          catch 
	                           _ -> L
	                          end
	                       end,
	  try
	        TreeDict_ = lists:flatten([cerl_trees:fold(FunctionForFolding,[],Core_) || {_,Core_} <- Core]),
	  	TreeDict = dict:from_list(TreeDict_),
	  	%io:format("TreeDict: ~p\n",[TreeDict_]),
	  	put(tree,TreeDict)
	  catch
	   _ -> put(tree,[])
	  end;
        _->ok
  end,
  case find_succ_typings(State) of
    {fixpoint, State1} -> State1;
    {not_fixpoint, NotFixpoint1, State1} ->
      Callgraph = State1#st.callgraph,
      NotFixpoint2 = [lookup_name(F, Callgraph) || F <- NotFixpoint1],
      ModulePostorder = 
	dialyzer_callgraph:module_postorder_from_funs(NotFixpoint2, Callgraph),
      case refine_succ_typings(ModulePostorder, State1) of
	{fixpoint, State2} ->
	  State2;
	{not_fixpoint, NotFixpoint3, State2} ->
	  Callgraph1 = State2#st.callgraph,
	  %% Need to reset the callgraph.
	  NotFixpoint4 = [lookup_name(F, Callgraph1) || F <- NotFixpoint3],
	  Callgraph2 = dialyzer_callgraph:reset_from_funs(NotFixpoint4, 
							  Callgraph1),
	  get_refined_success_typings(State2#st{callgraph = Callgraph2})
      end
  end.


get_all_core(Callgraph,Codeserver) ->
  case dialyzer_callgraph:take_scc(Callgraph) of
    {ok, SCC, NewCallgraph} ->
        SCC_Info = [dialyzer_codeserver:lookup_mfa_code({M,F,A}, Codeserver)
	      || {M,F,A} <- SCC],
	lists:flatten([SCC_Info | get_all_core(NewCallgraph,Codeserver)]);
    none -> []
  end.

-type doc_plt() :: 'undefined' | dialyzer_plt:plt().
-spec get_warnings(dialyzer_callgraph:callgraph(), dialyzer_plt:plt(),
		   doc_plt(), dialyzer_codeserver:codeserver(), set(),
		   pid(), boolean()) ->
	 {[dial_warning()], dialyzer_plt:plt(), doc_plt()}.

get_warnings(Callgraph, Plt, DocPlt, Codeserver,
	     NoWarnUnused, Parent, BehavioursChk) ->
  InitState = #st{callgraph = Callgraph, codeserver = Codeserver,
		  no_warn_unused = NoWarnUnused, parent = Parent, plt = Plt},
  NewState = get_refined_success_typings(InitState),
  Mods = dialyzer_callgraph:modules(NewState#st.callgraph),
  CWarns = dialyzer_contracts:get_invalid_contract_warnings(Mods, Codeserver,
							    NewState#st.plt),
  get_warnings_from_modules(Mods, NewState, DocPlt, BehavioursChk, CWarns).

get_warnings_from_modules([M|Ms], State, DocPlt,
			  BehavioursChk, Acc) when is_atom(M) ->
  send_log(State#st.parent, io_lib:format("Getting warnings for ~w\n", [M])),
  #st{callgraph = Callgraph, codeserver = Codeserver,
      no_warn_unused = NoWarnUnused, plt = Plt} = State,
  ModCode = dialyzer_codeserver:lookup_mod_code(M, Codeserver),
  Records = dialyzer_codeserver:lookup_mod_records(M, Codeserver),
  Contracts = dialyzer_codeserver:lookup_mod_contracts(M, Codeserver),
  AllFuns = collect_fun_info([ModCode]),
  %% Check if there are contracts for functions that do not exist
  Warnings1 = 
    dialyzer_contracts:contracts_without_fun(Contracts, AllFuns, Callgraph),
  {RawWarnings2, FunTypes, RaceCode, PublicTables, NamedTables} =
    dialyzer_dataflow:get_warnings(ModCode, Plt, Callgraph, Records, NoWarnUnused),
  {NewAcc, Warnings2} = postprocess_dataflow_warns(RawWarnings2, State, Acc),
  Attrs = cerl:module_attrs(ModCode),
  Warnings3 = if BehavioursChk ->
		  dialyzer_behaviours:check_callbacks(M, Attrs,
						      Plt, Codeserver);
		 true -> []
	      end,
  NewDocPlt = insert_into_doc_plt(FunTypes, Callgraph, DocPlt),
  NewCallgraph =
    dialyzer_callgraph:renew_race_info(Callgraph, RaceCode, PublicTables,
                                       NamedTables),
  State1 = st__renew_state_calls(NewCallgraph, State),
  get_warnings_from_modules(Ms, State1, NewDocPlt, BehavioursChk,
			    [Warnings1, Warnings2, Warnings3|NewAcc]);
get_warnings_from_modules([], #st{plt = Plt}, DocPlt, _, Acc) ->
  {lists:flatten(Acc), Plt, DocPlt}.

postprocess_dataflow_warns(RawWarnings, State, WarnAcc) ->
  postprocess_dataflow_warns(RawWarnings, State, WarnAcc, []).

postprocess_dataflow_warns([], _State, WAcc, Acc) ->
  {WAcc, lists:reverse(Acc)};
postprocess_dataflow_warns([{?WARN_CONTRACT_RANGE, {CallF, CallL}, Msg}|Rest],
			   #st{codeserver = Codeserver} = State, WAcc, Acc) ->
  {contract_range, [Contract, M, F, A, ArgStrings, CRet]} = Msg,
  case dialyzer_codeserver:lookup_mfa_contract({M,F,A}, Codeserver) of
    {ok, {{ContrF, _ContrL} = FileLine, _C}} ->
      case CallF =:= ContrF of
	true ->
	  NewMsg = {contract_range, [Contract, M, F, ArgStrings, CallL, CRet]},
	  W = {?WARN_CONTRACT_RANGE, FileLine, NewMsg},
	  Filter =
	    fun({?WARN_CONTRACT_TYPES, FL, _}) when FL =:= FileLine -> false;
	       (_) -> true
	    end,
	  FilterWAcc = lists:filter(Filter, WAcc),
	  postprocess_dataflow_warns(Rest, State, FilterWAcc, [W|Acc]);
	false ->
	  postprocess_dataflow_warns(Rest, State, WAcc, Acc)
      end;
    error ->
      %% The contract is not in a module that is currently under analysis.
      %% We display the warning in the file/line of the call.
      NewMsg = {contract_range, [Contract, M, F, ArgStrings, CallL, CRet]},
      W = {?WARN_CONTRACT_RANGE, {CallF, CallL}, NewMsg},
      postprocess_dataflow_warns(Rest, State, WAcc, [W|Acc])
  end;
postprocess_dataflow_warns([W|Rest], State, Wacc, Acc) ->
  postprocess_dataflow_warns(Rest, State, Wacc, [W|Acc]).
  
refine_succ_typings(ModulePostorder, State) ->
  ?debug("Module postorder: ~p\n", [ModulePostorder]),
  refine_succ_typings(ModulePostorder, State, []).

refine_succ_typings([SCC|SCCs], State, Fixpoint) ->
  Msg = io_lib:format("Dataflow of one SCC: ~w\n", [SCC]),
  send_log(State#st.parent, Msg),
  ?debug("~s\n", [Msg]),
  {NewState, FixpointFromScc} =
    case SCC of
      [M] -> refine_one_module(M, State);
      [_|_] -> refine_one_scc(SCC, State)
    end,
  NewFixpoint = ordsets:union(Fixpoint, FixpointFromScc),
  refine_succ_typings(SCCs, NewState, NewFixpoint);
refine_succ_typings([], State, Fixpoint) ->
  case Fixpoint =:= [] of
    true -> {fixpoint, State};
    false -> {not_fixpoint, Fixpoint, State}
  end.

-spec refine_one_module(module(), #st{}) -> {#st{}, [label()]}. % ordset

refine_one_module(M, State) ->
  #st{callgraph = Callgraph, codeserver = CodeServer, plt = PLT} = State,
  ModCode = dialyzer_codeserver:lookup_mod_code(M, CodeServer),
  AllFuns = collect_fun_info([ModCode]),
  FunTypes = get_fun_types_from_plt(AllFuns, State),
  Records = dialyzer_codeserver:lookup_mod_records(M, CodeServer),
  {NewFunTypes, RaceCode, PublicTables, NamedTables} =
    dialyzer_dataflow:get_fun_types(ModCode, PLT, Callgraph, Records),
  NewCallgraph =
    dialyzer_callgraph:renew_race_info(Callgraph, RaceCode, PublicTables,
                                       NamedTables),
  case reached_fixpoint(FunTypes, NewFunTypes) of
    true ->
      State1 = st__renew_state_calls(NewCallgraph, State),
      {State1, ordsets:new()};
    {false, NotFixpoint} ->
      ?debug("Not fixpoint\n", []),
      NewState = insert_into_plt(dict:from_list(NotFixpoint), State,State#st.local_lbl),
      NewState1 = st__renew_state_calls(NewCallgraph, NewState),
      {NewState1, ordsets:from_list([FunLbl || {FunLbl,_Type} <- NotFixpoint])}
  end.

st__renew_state_calls(Callgraph, State) ->
  State#st{callgraph = Callgraph}.

refine_one_scc(SCC, State) ->
  refine_one_scc(SCC, State, []).

refine_one_scc(SCC, State, AccFixpoint) ->
  {NewState, FixpointFromScc} = refine_mods_in_scc(SCC, State, []),
  case FixpointFromScc =:= [] of
    true -> {NewState, AccFixpoint};
    false ->
      NewAccFixpoint = ordsets:union(AccFixpoint, FixpointFromScc),
      refine_one_scc(SCC, NewState, NewAccFixpoint)
  end.

refine_mods_in_scc([Mod|Mods], State, Fixpoint) ->
  {NewState, FixpointFromModule} = refine_one_module(Mod, State),
  NewFixpoint = ordsets:union(FixpointFromModule, Fixpoint),
  refine_mods_in_scc(Mods, NewState, NewFixpoint);
refine_mods_in_scc([], State, Fixpoint) ->
  {State, Fixpoint}.

reached_fixpoint(OldTypes, NewTypes) ->
  reached_fixpoint(OldTypes, NewTypes, false).

reached_fixpoint_strict(OldTypes, NewTypes) ->
  case reached_fixpoint(OldTypes, NewTypes, true) of
    true -> true;
    {false, _} -> false
  end.

reached_fixpoint(OldTypes0, NewTypes0, Strict) ->
  MapFun = fun(_Key, Type) ->
	       case is_failed_or_not_called_fun(Type) of
		 true -> failed_fun;
		 false -> erl_types:t_limit(Type, ?TYPE_LIMIT)
	       end
	   end,
  OldTypes = dict:map(MapFun, OldTypes0),
  NewTypes = dict:map(MapFun, NewTypes0),
  compare_types(OldTypes, NewTypes, Strict).

is_failed_or_not_called_fun(Type) ->
  erl_types:any_none([erl_types:t_fun_range(Type)|erl_types:t_fun_args(Type)]).

compare_types(Dict1, Dict2, Strict) ->  
  List1 = lists:keysort(1, dict:to_list(Dict1)),
  List2 = lists:keysort(1, dict:to_list(Dict2)),
  compare_types_1(List1, List2, Strict, []).

compare_types_1([{X, _Type1}|Left1], [{X, failed_fun}|Left2], 
		Strict, NotFixpoint) ->
  compare_types_1(Left1, Left2, Strict, NotFixpoint);
compare_types_1([{X, failed_fun}|Left1], [{X, _Type2}|Left2], 
		Strict, NotFixpoint) ->
  compare_types_1(Left1, Left2, Strict, NotFixpoint);
compare_types_1([{X, Type1}|Left1], [{X, Type2}|Left2], Strict, NotFixpoint) ->
  Res = case Strict of
	  true -> erl_types:t_is_equal(Type1, Type2);
	  false -> erl_types:t_is_subtype(Type1, Type2)
	end,
  case Res of
    true -> compare_types_1(Left1, Left2, Strict, NotFixpoint);
    false -> 
      ?debug("Failed fixpoint for ~w: ~s =/= ~s\n",
	     [X, erl_types:t_to_string(Type1), erl_types:t_to_string(Type2)]),
      compare_types_1(Left1, Left2, Strict, [{X, Type2}|NotFixpoint])
  end;
compare_types_1([_|Left1], List2, Strict, NotFixpoint) ->
  %% If the function was not called.
  compare_types_1(Left1, List2, Strict, NotFixpoint);
compare_types_1([], [], _Strict, NotFixpoint) ->
  case NotFixpoint =:= [] of
    true -> true;
    false -> {false, NotFixpoint}
  end.
  
 

find_succ_typings(State) ->
  find_succ_typings(State, []).

find_succ_typings(#st{callgraph = Callgraph, parent = Parent} = State,
		  NotFixpoint) ->
  case dialyzer_callgraph:take_scc(Callgraph) of
    {ok, SCC, NewCallgraph} ->
      Msg = io_lib:format("Typesig analysis for SCC: ~w\n", [format_scc(SCC)]),
      ?debug("~s", [Msg]),
      send_log(Parent, Msg),
      {NewState, NewNotFixpoint1} =
	analyze_scc(SCC, State#st{callgraph = NewCallgraph}),
      NewNotFixpoint2 = ordsets:union(NewNotFixpoint1, NotFixpoint),
      find_succ_typings(NewState, NewNotFixpoint2);
    none ->
      ?debug("==================== Typesig done ====================\n\n", []),
      case NotFixpoint =:= [] of
	true -> {fixpoint, State};
	false -> {not_fixpoint, NotFixpoint, State}
      end
  end.

analyze_scc(SCC, #st{codeserver = Codeserver} = State) ->
  %io:format("Callgraph: ~p\n",[State#st.callgraph]),
  SCC_Info = [{MFA, 
	       dialyzer_codeserver:lookup_mfa_code(MFA, Codeserver),
	       dialyzer_codeserver:lookup_mod_records(M, Codeserver)}
	      || {M, _, _} = MFA <- SCC],
  Contracts1 = [{MFA, dialyzer_codeserver:lookup_mfa_contract(MFA, Codeserver)}
		|| {_, _, _} = MFA <- SCC],
  Contracts2 = [{MFA, Contract} || {MFA, {ok, Contract}} <- Contracts1],
  Contracts3 = orddict:from_list(Contracts2),
  {SuccTypes, PltContracts, NotFixpoint,LocalLbl} = 
    find_succ_types_for_scc(SCC_Info, Contracts3, State),
  %io:format("SuccTypes: ~p\n",[dict:to_list(SuccTypes)]),
  State1 = insert_into_plt(SuccTypes, State,LocalLbl),
  ContrPlt = dialyzer_plt:insert_contract_list(State1#st.plt, PltContracts),
  {State1#st{plt = ContrPlt}, NotFixpoint}.

find_succ_types_for_scc(SCC_Info, Contracts, 
			#st{codeserver = Codeserver, 
			    callgraph = Callgraph, plt = Plt, local_lbl = LocalLbl0} = State) ->
  %% Assume that the PLT contains the current propagated types
  AllFuns = collect_fun_info([Fun || {_MFA, {_Var, Fun}, _Rec} <- SCC_Info]),
  PropTypes = get_fun_types_from_plt(AllFuns, State),
  MFAs = [MFA || {MFA, {_Var, _Fun}, _Rec} <- SCC_Info],
  NextLabel = dialyzer_codeserver:get_next_core_label(Codeserver),
  Plt1 = dialyzer_plt:delete_contract_list(Plt, MFAs),
  %io:format("\n*******************\n\nLocalLbl0: ~w\n",[dict:to_list(LocalLbl0)]),
  {FunTypes,LocalLbl,InfoErrors} = dialyzer_typesig:analyze_scc(SCC_Info, NextLabel, 
  					  Callgraph, Plt1, PropTypes,LocalLbl0),
  case InfoErrors of
       [] -> ok;
       _ ->
          {ok, DeviceSerialR} = file:open("errors.temp", [read]),
	  Errors=io:get_line(DeviceSerialR,""),
	  ok = file:close(DeviceSerialR),
	  {ok,Tokens,_EndLine} = erl_scan:string(Errors++"."),
	  {ok,AbsForm} = erl_parse:parse_exprs(Tokens),
	  LblsErrorsPrev=
	    case erl_eval:exprs(AbsForm, erl_eval:new_bindings()) of
	         {value,Lbls_,_} -> Lbls_;
	         _ -> []
	    end,
	  LblsErrorList = [LblsError_ || {_,_,_,LblsError_,_,_} <-InfoErrors], % This could be really improved. There is a lot of information about the error, but only its labels are used.
	  %io:format("LblsErrorList: ~w\n",[LblsErrorList]),
	  LblsError = lists:foldl(
	                 fun(LblsError_, LblsErrorsPrev_) -> 
	                    join_lbl_errors(LblsError_,LblsErrorsPrev_) 
	                end, LblsErrorsPrev, LblsErrorList),
	  %LblsError = join_lbl_errors(LblsError_,LblsErrorsPrev),
	  {ok, DeviceSerial} = file:open("errors.temp", [write]),
	  io:write(DeviceSerial,LblsError),
	  ok = file:close(DeviceSerial)
   end,
%  FunTypes = dialyzer_typesig:analyze_scc(SCC_Info, NextLabel, 
%  					  Callgraph, Plt1, PropTypes),
%  LocalLbl = dict:new(),
  %io:format("FunTypes: ~p\nLocalLbl: ~p\n",[FunTypes,LocalLbl]),
  %io:format("FunTypes: ~p\nLocalLbl: ~w\n",[dict:to_list(FunTypes),dict:to_list(LocalLbl)]),
  AllFunSet = sets:from_list([X || {X, _} <- AllFuns]),
  FilteredFunTypes = dict:filter(fun(X, _) ->
				      sets:is_element(X, AllFunSet) 
				  end, FunTypes),
  %% Check contracts
  PltContracts = dialyzer_contracts:check_contracts(Contracts, Callgraph, 
						    FilteredFunTypes),
  ContractFixpoint =
    lists:all(fun({MFA, _C}) ->
		  %% Check the non-deleted PLT
		  case dialyzer_plt:lookup_contract(Plt, MFA) of
		    none -> false;
		    {value, _} -> true
		  end
	      end, PltContracts),
  case (ContractFixpoint andalso 
	reached_fixpoint_strict(PropTypes, FilteredFunTypes)) of
    true ->
      {FilteredFunTypes, PltContracts, [], LocalLbl};
    false ->
      ?debug("Not fixpoint for: ~w\n", [AllFuns]),
      {FilteredFunTypes, PltContracts,
       ordsets:from_list([Fun || {Fun, _Arity} <- AllFuns]),
       LocalLbl}
  end.
  
join_lbl_errors(Lbls,[PrevLbl|PrevLbls])->
   SLbls = sets:from_list(Lbls),
   SPrevLbl =  sets:from_list(PrevLbl),
   case sets:is_disjoint(SLbls,SPrevLbl) of
        true -> [PrevLbl|join_lbl_errors(Lbls,PrevLbls)];
        false -> 
           case sets:is_subset(SLbls,SPrevLbl) of
                true -> [PrevLbl|PrevLbls];
                false -> 
                   case sets:is_subset(SPrevLbl,SLbls) of
                        true -> [Lbls|PrevLbls];
                        false -> [PrevLbl|join_lbl_errors(Lbls,PrevLbls)]
                   end
           end   
   end;
join_lbl_errors(Lbls,[])->
   [Lbls].

get_fun_types_from_plt(FunList, State) ->
  get_fun_types_from_plt(FunList, State, dict:new()).

get_fun_types_from_plt([{FunLabel, Arity}|Left], State, Map) ->
  Type = lookup_fun_type(FunLabel, Arity, State),
  get_fun_types_from_plt(Left, State, dict:store(FunLabel, Type, Map));
get_fun_types_from_plt([], _State, Map) ->
  Map.

collect_fun_info(Trees) ->
  collect_fun_info(Trees, []).

collect_fun_info([Tree|Trees], List) ->
  Fun = fun(SubTree, Acc) ->
	    case cerl:is_c_fun(SubTree) of
	      true ->
		[{cerl_trees:get_label(SubTree), cerl:fun_arity(SubTree)}|Acc];
	      false -> Acc
	    end
	end,
  collect_fun_info(Trees, cerl_trees:fold(Fun, List, Tree));
collect_fun_info([], List) ->
  List.

lookup_fun_type(Label, Arity, #st{callgraph = Callgraph, plt = Plt}) ->
  ID = lookup_name(Label, Callgraph),
  case dialyzer_plt:lookup(Plt, ID) of
    none -> erl_types:t_fun(Arity, erl_types:t_any());
    {value, {RetT, ArgT}} -> erl_types:t_fun(ArgT, RetT)
  end.

insert_into_doc_plt(_FunTypes, _Callgraph, undefined) ->
  undefined;
insert_into_doc_plt(FunTypes, Callgraph, DocPlt) ->
  SuccTypes = format_succ_types(FunTypes, Callgraph),
  dialyzer_plt:insert_list(DocPlt, SuccTypes).

insert_into_plt(SuccTypes0, #st{callgraph = Callgraph, plt = Plt, local_lbl = LocalLbl0} = State,LocalLbl) ->
  SuccTypes = format_succ_types(SuccTypes0, Callgraph),
  debug_pp_succ_typings(SuccTypes),
  %io:format("SuccTypes0: ~p\n",[dict:to_list(SuccTypes0)]),
  %io:format("SuccTypes: ~p\n",[SuccTypes]),
  %io:format("LocalLbl: ~p\n",[dict:to_list(LocalLbl)]),
  FormatLbl = format_lbl(LocalLbl,Callgraph),
  MergeFunction = fun(_,V1,V2) -> appendPairs(V1,V2) end,
  MergedLocalLbl = dict:merge(MergeFunction,LocalLbl0,dict:from_list(FormatLbl)),
  %io:format("FormatLbl: ~p\n",[FormatLbl]),
  State#st{plt = dialyzer_plt:insert_list(Plt, SuccTypes), 
           local_lbl = MergedLocalLbl}.


appendPairs([H1|T1],[H2|T2])->
  [H1++H2|appendPairs(T1,T2)];
appendPairs([],[]) -> [].

format_succ_types(SuccTypes, Callgraph) ->
  format_succ_types(dict:to_list(SuccTypes), Callgraph, []).

format_succ_types([{Label, Type0}|Left], Callgraph, Acc) ->
  Type = erl_types:t_limit(Type0, ?TYPE_LIMIT+1),
  Id = lookup_name(Label, Callgraph),
  NewTuple = {Id, {erl_types:t_fun_range(Type), erl_types:t_fun_args(Type)}},
  format_succ_types(Left, Callgraph, [NewTuple|Acc]);
format_succ_types([], _Callgraph, Acc) ->
  Acc.
  
format_lbl(LocalLbl,Callgraph) ->
  format_lbl(dict:to_list(LocalLbl), Callgraph, []).
  
format_lbl([{Label={c,var,_,_}, Lbls}|Left], Callgraph, Acc) ->
  %io:format("{Label, Lbls}: ~w\n",[{Label, Lbls}]),
%  Lbls = lists:foldl(fun (L=[_|_],LAcc) -> [L|LAcc];
%                         ([],LAcc) -> LAcc 
%                     end,[],Lbls0),
  Id = lookup_name(erl_types:t_var_name(Label), Callgraph),
  %io:format("Id: ~w\n",[Id]),
  NewTuple = {Id, Lbls},
  format_lbl(Left, Callgraph, [NewTuple|Acc]);
format_lbl([_|_], _, Acc) ->
  Acc;
format_lbl([], _Callgraph, Acc) ->
  Acc.

-ifdef(DEBUG).
debug_pp_succ_typings(SuccTypes) ->
  ?debug("Succ typings:\n", []),
  [?debug("  ~w :: ~s\n", 
	  [MFA, erl_types:t_to_string(erl_types:t_fun(ArgT, RetT))])
   || {MFA, {RetT, ArgT}} <- SuccTypes],
  ?debug("Contracts:\n", []),
  [?debug("  ~w :: ~s\n", 
	  [MFA, erl_types:t_to_string(erl_types:t_fun(ArgT, RetFun(ArgT)))])
   || {MFA, {contract, RetFun, ArgT}} <- SuccTypes],
  ?debug("\n", []),
  ok.
-else.
debug_pp_succ_typings(_) ->
  ok.
-endif.

lookup_name(F, CG) ->
  case dialyzer_callgraph:lookup_name(F, CG) of
    error -> F;
    {ok, Name} -> Name
  end.

send_log(none, _Msg) ->
  ok;
send_log(Parent, Msg) ->
  Parent ! {self(), log, lists:flatten(Msg)},
  ok.

format_scc(SCC) ->
  [MFA || {_M, _F, _A} = MFA <- SCC].

%% ============================================================================
%%
%%  Debug interface.
%%
%% ============================================================================

-spec doit(atom() | file:filename()) -> 'ok'.

doit(Module) ->
  {ok, AbstrCode} = dialyzer_utils:get_abstract_code_from_src(Module),
  {ok, Code} = dialyzer_utils:get_core_from_abstract_code(AbstrCode),
  {ok, Records} = dialyzer_utils:get_record_and_type_info(AbstrCode),
  %% contract typing info in dictionary format
  {ok, Contracts} =
    dialyzer_utils:get_spec_info(cerl:concrete(cerl:module_name(Code)),
                                 AbstrCode, Records),
  Sigs0 = get_top_level_signatures(Code, Records, Contracts),
  M = if is_atom(Module) ->  
	  list_to_atom(filename:basename(atom_to_list(Module)));
	 is_list(Module) -> 
	  list_to_atom(filename:basename(Module))
      end,
  Sigs1 = [{{M, F, A}, Type} || {{F, A}, Type} <- Sigs0],
  Sigs = ordsets:from_list(Sigs1),
  io:format("==================== Final result ====================\n\n", []),
  pp_signatures(Sigs, Records),
  ok.

-spec get_top_level_signatures(cerl:c_module(), dict(), dict()) ->
	 [{{atom(), arity()}, erl_types:erl_type()}].

get_top_level_signatures(Code, Records, Contracts) ->
  Tree = cerl:from_records(Code),
  {LabeledTree, NextLabel} = cerl_trees:label(Tree),
  Plt = get_def_plt(),
  ModuleName = cerl:atom_val(cerl:module_name(LabeledTree)),
  Plt1 = dialyzer_plt:delete_module(Plt, ModuleName),
  Plt2 = analyze_module(LabeledTree, NextLabel, Plt1, Records, Contracts),
  M = cerl:concrete(cerl:module_name(Tree)),
  Functions = [{M, cerl:fname_id(V), cerl:fname_arity(V)} 
	       || {V, _F} <- cerl:module_defs(LabeledTree)],
  %% First contracts check
  AllContracts = dict:fetch_keys(Contracts),
  ErrorContracts = AllContracts -- Functions,  
  lists:foreach(fun(C) -> 
		    io:format("Contract for non-existing function: ~w\n",[C])
		end, ErrorContracts),
  Types = [{MFA, dialyzer_plt:lookup(Plt2, MFA)} || MFA <- Functions],
  Sigs = [{{F, A}, erl_types:t_fun(ArgT, RetT)} 
	  || {{_M, F, A}, {value, {RetT, ArgT}}} <- Types],
  ordsets:from_list(Sigs).

get_def_plt() ->
  try 
    dialyzer_plt:from_file(dialyzer_plt:get_default_plt())
  catch
    error:no_such_file -> dialyzer_plt:new();
    throw:{dialyzer_error, _} -> dialyzer_plt:new()
  end.

pp_signatures([{{_, module_info, 0}, _}|Left], Records) -> 
  pp_signatures(Left, Records);
pp_signatures([{{_, module_info, 1}, _}|Left], Records) -> 
  pp_signatures(Left, Records);
pp_signatures([{{M, F, _A}, Type}|Left], Records) ->
  TypeString =
    case cerl:is_literal(Type) of
%% Commented out so that dialyzer does not complain
%%      false -> 
%%        "fun(" ++ String = erl_types:t_to_string(Type, Records),
%%        string:substr(String, 1, length(String)-1);
      true ->
	io_lib:format("~w", [cerl:concrete(Type)])
    end,
  io:format("~w:~w~s\n", [M, F, TypeString]),
  pp_signatures(Left, Records);
pp_signatures([], _Records) ->
  ok.

-ifdef(DEBUG_PP).
debug_pp(Tree, _Map) -> 
  Tree1 = strip_annotations(Tree),
  io:put_chars(cerl_prettypr:format(Tree1)),
  io:nl().  

strip_annotations(Tree) ->
  cerl_trees:map(fun(T) ->
		     case cerl:is_literal(T) orelse cerl:is_c_values(T) of
		       true -> cerl:set_ann(T, []);
		       false ->
			 Label = cerl_trees:get_label(T),
			 cerl:set_ann(T, [{'label', Label}])
		     end
		 end, Tree).
-else.
debug_pp(_Tree, _Map) ->
  ok.
-endif. % DEBUG_PP

%%
%% Analysis of a single module
%%
analyze_module(LabeledTree, NextLbl, Plt, Records, Contracts) ->
  debug_pp(LabeledTree, dict:new()),
  CallGraph1 = dialyzer_callgraph:new(),
  CallGraph2 = dialyzer_callgraph:scan_core_tree(LabeledTree, CallGraph1),
  {CallGraph3, _Ext} = dialyzer_callgraph:remove_external(CallGraph2),
  CallGraph4 = dialyzer_callgraph:finalize(CallGraph3),
  CodeServer1 = dialyzer_codeserver:new(),
  Mod = cerl:concrete(cerl:module_name(LabeledTree)),
  CodeServer2 = dialyzer_codeserver:insert(Mod, LabeledTree, CodeServer1),
  CodeServer3 = dialyzer_codeserver:set_next_core_label(NextLbl, CodeServer2),
  CodeServer4 = dialyzer_codeserver:store_records(Mod, Records, CodeServer3),
  CodeServer5 = dialyzer_codeserver:store_contracts(Mod, Contracts, CodeServer4),
  Res = analyze_callgraph(CallGraph4, Plt, CodeServer5),
  dialyzer_callgraph:delete(CallGraph4),
  dialyzer_codeserver:delete(CodeServer5),
  Res.

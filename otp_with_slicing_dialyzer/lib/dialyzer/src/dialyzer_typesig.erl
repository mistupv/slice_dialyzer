%% -*- erlang-indent-level: 2 -*-
%%-----------------------------------------------------------------------
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2006-2010. All Rights Reserved.
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
%%% File    : dialyzer_typesig.erl
%%% Author  : Tobias Lindahl <tobiasl@it.uu.se>
%%% Description :
%%%
%%% Created : 25 Apr 2005 by Tobias Lindahl <tobiasl@it.uu.se>
%%%-------------------------------------------------------------------



%crear un diccionari de deps (idenitifacodr de contraints) aon se crea var_lbl per a q quant pete una retriccio buscar el historial correponent a ixa restriccio crea en el apply****** CREC QUE LE QUE  VOLIA DIR ESTA COMENÇAT EN State2 = State#state{ctrs_lbl = DictCtrs},





-module(dialyzer_typesig).

-export([analyze_scc/6]).
-export([get_safe_underapprox/2]).

-import(erl_types,
	[t_any/0, t_atom/0, t_atom_vals/1,
	 t_binary/0, t_bitstr/0, t_bitstr/2, t_bitstr_concat/1, t_boolean/0,
	 t_collect_vars/1, t_cons/2, t_cons_hd/1, t_cons_tl/1,
	 t_float/0, t_from_range/2, t_from_term/1,
	 t_fun/0, t_fun/2, t_fun_args/1, t_fun_range/1,
	 t_has_var/1,
	 t_inf/2, t_inf/3, t_integer/0,
	 t_is_any/1, t_is_atom/1, t_is_atom/2, t_is_cons/1, t_is_equal/2,
	 t_is_float/1, t_is_fun/1,
	 t_is_integer/1, t_non_neg_integer/0,
	 t_is_list/1, t_is_nil/1, t_is_none/1, t_is_number/1,

	 t_is_subtype/2, t_limit/2, t_list/0, t_list/1,
	 t_list_elements/1, t_nonempty_list/1, t_maybe_improper_list/0,
	 t_module/0, t_number/0, t_number_vals/1,
	 t_opaque_match_record/2, t_opaque_matching_structure/2,
	 t_opaque_from_records/1,
	 t_pid/0, t_port/0, t_product/1, t_reference/0,
	 t_subst/2, t_subtract/2, t_subtract_list/2, t_sup/1, t_sup/2,
	 t_timeout/0, t_tuple/0, t_tuple/1,
	 t_unify/3, t_var/1, t_var_name/1,
	 t_none/0, t_unit/0]).

-include("dialyzer.hrl").

%%-----------------------------------------------------------------------------

-type dep()      :: integer().  %% type variable names used as constraint ids
-type type_var() :: erl_types:erl_type(). %% actually: {'c','var',_,_}

-record(fun_var, {'fun' :: fun((_) -> erl_types:erl_type()), deps :: [dep()]}).

-type constr_op()    :: 'eq' | 'sub'.
-type fvar_or_type() :: #fun_var{} | erl_types:erl_type().

-record(constraint, {lhs  :: erl_types:erl_type(),
		     op   :: constr_op(),
		     rhs  :: fvar_or_type(),
		     deps :: [dep()]}).

-type constraint() :: #constraint{}.

-record(constraint_slicing, {cs  :: constraint(),
		     lbls  :: [integer()]}).

-type constraint_slicing() :: #constraint_slicing{}.

-record(constraint_list, {type :: 'conj' | 'disj',
			  list :: [constr()],
			  deps :: [dep()],
			  id   :: {'list', dep()}}).

-type constraint_list() :: #constraint_list{}.

-record(constraint_list_slicing, {type :: 'conj' | 'disj',
			  list :: [constr_slicing()],
			  deps :: [dep()],
			  id   :: {'list', dep()}}).

-type constraint_list_slicing() :: #constraint_list_slicing{}.

-record(constraint_ref, {id :: type_var(), deps :: [dep()]}).

-type constraint_ref() :: #constraint_ref{}.

-type constr() :: constraint() | constraint_list() | constraint_ref().

-type constr_slicing() :: constraint_slicing() | constraint_list_slicing() | constraint_ref().

-type typesig_scc()    :: [{mfa(), {cerl:c_var(), cerl:c_fun()}, dict()}].
-type typesig_funmap() :: [{type_var(), type_var()}]. %% Orddict

-record(state, {callgraph                  :: dialyzer_callgraph:callgraph(),
		cs            = []         :: [constr()],
		cs_slicing    = []         :: [constr_slicing()],
		cmap          = dict:new() :: dict(),
		cmap_slicing  = dict:new() :: dict(),
		fun_map       = []         :: typesig_funmap(),
		fun_arities   = dict:new() :: dict(),
		in_match      = false      :: boolean(),
		in_guard      = false      :: boolean(),
		module                     :: module(),
		name_map      = dict:new() :: dict(),
		next_label                 :: label(),
		non_self_recs = []         :: [label()],
		plt                        :: dialyzer_plt:plt(),
		prop_types    = dict:new() :: dict(),
		records       = dict:new() :: dict(),
		opaques       = []         :: [erl_types:erl_type()],
		scc           = []         :: [type_var()],
		fun_lbl                    :: dict(),
		var_lbl       = dict:new() :: dict()}).

%%-----------------------------------------------------------------------------

-define(TYPE_LIMIT, 4).
-define(INTERNAL_TYPE_LIMIT, 5).

%%-define(DEBUG, true).
%%-define(DEBUG_CONSTRAINTS, true).
%%-define(TO_DOT,true).
-ifdef(DEBUG).
-define(DEBUG_NAME_MAP, true).
-endif.
%%-define(DEBUG_NAME_MAP, true).

-ifdef(DEBUG).
-define(debug(__String, __Args), io:format(__String, __Args)).
-else.
-define(debug(__String, __Args), ok).
-endif.

%% ============================================================================
%%
%%  The analysis.
%%
%% ============================================================================

%%-----------------------------------------------------------------------------
%% Analysis of strongly connected components.
%%
%% analyze_scc(SCC, NextLabel, CallGraph, PLT, PropTypes) -> FunTypes
%%
%% SCC       - [{MFA, Def, Records}]
%%             where Def = {Var, Fun} as in the Core Erlang module definitions.
%%                   Records = dict(RecName, {Arity, [{FieldName, FieldType}]})
%% NextLabel - An integer that is higher than any label in the code.
%% CallGraph - A callgraph as produced by dialyzer_callgraph.erl
%%             Note: The callgraph must have been built with all the
%%                   code that the SCC is a part of.
%% PLT       - A dialyzer PLT. This PLT should contain available information
%%             about functions that can be called by this SCC.
%% PropTypes - A dictionary.
%% FunTypes  - A dictionary.
%%-----------------------------------------------------------------------------

-spec analyze_scc(typesig_scc(), label(),
		  dialyzer_callgraph:callgraph(),
		  dialyzer_plt:plt(), dict(), dict()) -> dict().

analyze_scc(SCC, NextLabel, CallGraph, Plt, PropTypes,FunLbl) ->
  assert_format_of_scc(SCC),
  State1 = new_state(SCC, NextLabel, CallGraph, Plt, PropTypes, FunLbl),
  DefSet = add_def_list([ Var || {_MFA, {Var, _Fun}, _Rec} <- SCC],
  						 [], {sets:new(),dict:new()}),
  put(cases,[]),
  State2 = traverse_scc(SCC, DefSet, State1),
  [{{_,Fun,Arity},_,_}|_] = SCC,%{Fun,Arity}={module_info, 0},
  %-> DEBUG_INFO
%  case lists:member({Fun,Arity},[{module_info, 0},{module_info, 1}]) of
%       true->ok;
%       false->
%	%  pp_constraints_slicing(State2#state.cs_slicing,State2),
%	  io:format("\n+++++++++++++++++++++++++++++++++++++++++++++\n",[]),
%	  io:format("\nFinal constraints slicing:~n~p~n",[State2#state.cs_slicing]),
%	  io:format("\nFinal constraints:~n~p~n",[State2#state.cs]),
%	  io:format("\nFinal mapping slicing:~n",[]),
%	  ppDictCtrs(dict:to_list(State2#state.cmap_slicing),ini),
%	  io:format("\nFinal mapping:~n",[]),
%	  ppDictCtrs(dict:to_list(State2#state.cmap),ini),
%	  io:format("\n+++++++++++++++++++++++++++++++++++++++++++++\n",[])
%  end,
  %<- DEBUG_INFO
  State3 = state__finalize(State2),
  Funs = state__scc(State3),
  %pp_constrs_scc(Funs, State3),
  constraints_to_dot_scc(Funs, State3),
  {MapFun,LblFun,E} = solve(Funs, State3),
  %io:format("\nE:~p\n",[E]),
  case lists:member({Fun,Arity},[{module_info, 0},{module_info, 1}]) of
       true -> {MapFun,dict:new(),E};
       false -> {MapFun,LblFun,E}
   end.

assert_format_of_scc([{_MFA, {_Var, _Fun}, _Records}|Left]) ->
  assert_format_of_scc(Left);
assert_format_of_scc([]) ->
  ok.
  

%-> DEBUG_INFO
%ppDictCtrs(Dict,ini)->
%	io:format("[\n",[]),
%	ppDictCtrs(Dict),
%	io:format("]\n",[]).
% 
%  
%ppDictCtrs([{Key,Var}|Dicts]) ->
%	io:format("{\n\t~p,\n",[Key]),
%	ppCtrs(Var),
%	io:format("},\n",[]),
%	ppDictCtrs(Dicts);
%ppDictCtrs([])->io:format("\n",[]).
%
%
%ppCtrs({constraint_list_slicing,Type,Cs,_,_}) -> 
%	io:format("\t[~p\n",[Type]),
%	[begin ppCtrs(C),io:format("\n",[]) end|| C<-Cs],
%	io:format("\t],\n",[]);
%	
%ppCtrs({constraint_list,Type,Cs,_,_}) ->
%	io:format("\t[~p\n",[Type]),
%	[begin ppCtrs(C),io:format("\n",[]) end || C<-Cs],
%	io:format("\t],\n",[]);
%	
%ppCtrs({constraint,Lhs,Op,Rhs,_}) ->
%	io:format("\t~p ~p ~p",[Lhs,Op,Rhs]);
%	
%ppCtrs({constraint_slicing,C,Lbl}) ->
%	ppCtrs(C),io:format(" LABELS: ~w",[Lbl]);
%	
%ppCtrs({constraint_ref,Id,Deps}) ->
%	io:format("\tREF:~p ~p",[Id,Deps]).
%<- DEBUG_INFO



%% ============================================================================
%%
%%  Gets the constraints by traversing the code.
%%
%% ============================================================================

traverse_scc([{MFA, Def, Rec}|Left], DefSet, AccState) ->
  %-> DEBUG_INFO
%  io:format("\n****************\nTreating: ~p\n\n",[MFA]),
  %<- DEBUG_INFO
  %io:format("fun_lbl: \n"),
  %ppDictSol(dict:to_list(AccState#state.fun_lbl)),
  TmpState1 = state__set_rec_dict(AccState, Rec),
  TmpState2 = state__set_opaques(TmpState1, MFA),
  FooAtom = cerl:set_ann(cerl:c_atom(foo),[{label_slicing,-2}]),
  DummyLetrec_ = cerl:c_letrec([Def],FooAtom),
  DummyLetrec = cerl:set_ann(DummyLetrec_,[{label_slicing,-1}]),
%  FunctionRemoveAnn = fun (T) -> cerl:set_ann(T,[{ls,cerl_trees_:get_label(T)}]) end,
%  FunctionForFolding = fun (T,L) -> 
%                          [{cerl_trees_:get_label(T),cerl_trees:map(FunctionRemoveAnn,T)}|L] 
%                       end,
%  try
%  	TreeDict = dict:from_list(cerl_trees:fold(FunctionForFolding,[],DummyLetrec)),
%  	put(tree,TreeDict)
%  catch
%   _ -> put(tree,[])
%  end,
  {NewAccState, _, _} = traverse(DummyLetrec, DefSet, TmpState2),
  traverse_scc(Left, DefSet, NewAccState);
traverse_scc([], _DefSet, AccState) ->
  AccState.

traverse(Tree, DefinedVars, State) ->
  ?debug("Handling ~p\n", [cerl:type(Tree)]),
  case cerl:type(Tree) of
    alias ->
      Var = cerl:alias_var(Tree),
      Pat = cerl:alias_pat(Tree),
      DefinedVars1 = add_def(Var, [cerl_trees_:get_label(Tree)], DefinedVars),
      {State1, PatVar,LblPat} = traverse(Pat, DefinedVars1, State),
      State2 = state__store_conj_slicing(mk_var(Var), eq, PatVar, [cerl_trees_:get_label(Tree)|LblPat], State1),
      {State2, PatVar,[cerl_trees_:get_label(Tree)|LblPat]};
    apply ->
      Args = cerl:apply_args(Tree),
      Arity = length(Args),
      Op = cerl:apply_op(Tree),
      {State0, ArgTypes,ArgLbl} = traverse_list(Args, DefinedVars, State),
      %io:format("Args: ~p\nArgLbl:~w \nArgTypes:~p\n",[Args,ArgLbl,ArgTypes]),
      {State1, OpType,OpLbl} = traverse(Op, DefinedVars, State0),
      {State2, FunType} = state__get_fun_prototype(OpType, Arity, State1),
      State3 = state__store_conj_slicing(FunType, eq, OpType, [cerl_trees_:get_label(Tree)|OpLbl], State2),
      State4 = state__store_conj_slicing(mk_var(Tree), sub, t_fun_range(FunType),
				 [cerl_trees_:get_label(Tree)], State3),
      %io:format("ArgTypes: ~w ArgLbl:~w\n",[ArgTypes,ArgLbl]),
      State5 = state__store_conj_lists_slicing(ArgTypes, sub, t_fun_args(FunType),
				       [cerl_trees_:get_label(Tree)], ArgLbl, State4),
      case state__lookup_apply(Tree, State) of
		unknown ->
		  {State5, mk_var(Tree),[cerl_trees_:get_label(Tree)]};
		FunLabels ->
		  case get_apply_constr(FunType, FunLabels, mk_var(Tree), ArgTypes,
		        [cerl_trees_:get_label(Tree)],
		        %JJJ: ELS ARGUMENTS DUEN LA ETIQUETA DE LA OPERACIO APLICADA. SEGUR?
		        [OpLbl++ArgLbl_ || ArgLbl_<-ArgLbl], State5) of
		        %ArgLbl, State5) of
		    {error, State6_} -> {State6_, mk_var(Tree),[cerl_trees_:get_label(Tree)]};
		    {ok, State6} -> {State6, mk_var(Tree),[cerl_trees_:get_label(Tree)]}
		  end
      end;
    binary ->
      {State1, SegTypes,_} = traverse_list(cerl:binary_segments(Tree),
					 DefinedVars, State),
      Type = mk_fun_var(fun(Map) ->
			    TmpSegTypes = lookup_type_list(SegTypes, Map),
			    t_bitstr_concat(TmpSegTypes)
			end, SegTypes),
      {state__store_conj(mk_var(Tree), sub, Type, State1), mk_var(Tree),[cerl_trees_:get_label(Tree)]};
    bitstr ->
      Size = cerl:bitstr_size(Tree),
      UnitVal = cerl:int_val(cerl:bitstr_unit(Tree)),
      Val = cerl:bitstr_val(Tree),
      {State1, [SizeType, ValType],_} =
		traverse_list([Size, Val], DefinedVars, State),
      {State2, TypeConstr} =
		case cerl:bitstr_bitsize(Tree) of
		  all -> {State1, t_bitstr(UnitVal, 0),[cerl_trees_:get_label(Tree)]};
		  utf -> {State1, t_binary(),[cerl_trees_:get_label(Tree)]}; % contains an integer number of bytes
		  N when is_integer(N) -> {State1, t_bitstr(0, N), [cerl_trees_:get_label(Tree)]};
		  any -> % Size is not a literal
		    {state__store_conj(SizeType, sub, t_non_neg_integer(), State1),%JJJ Aqui falta meter un slice, pero no se lo que es un bitstr :)
		     mk_fun_var(bitstr_constr(SizeType, UnitVal), [SizeType]),[cerl_trees_:get_label(Tree)]}
		end,
      ValTypeConstr =
		case cerl:concrete(cerl:bitstr_type(Tree)) of
		  binary -> TypeConstr;
		  float ->
		    case state__is_in_match(State1) of
		      true -> t_float();
		      false -> t_number()
		    end;
		  integer ->
		    case state__is_in_match(State1) of
		      true ->
			Flags = cerl:concrete(cerl:bitstr_flags(Tree)),
			mk_fun_var(bitstr_val_constr(SizeType, UnitVal, Flags),
				   [SizeType]);
		      false -> t_integer()
		    end;
		  utf8  -> t_integer();
		  utf16 -> t_integer();
		  utf32 -> t_integer()
		end,
      State3 = state__store_conj_slicing(ValType, sub, ValTypeConstr,[cerl_trees_:get_label(Tree)],  State2),%JJJ No revisado
      State4 = state__store_conj_slicing(mk_var(Tree), sub, TypeConstr,[cerl_trees_:get_label(Tree)],  State3),%JJJ No revisado
      {State4, mk_var(Tree),[cerl_trees_:get_label(Tree)]};
    'case' ->
      Arg = cerl:case_arg(Tree),
      Clauses = filter_match_fail(cerl:case_clauses(Tree)),
      {State1, ArgVar,ArgLbl} = traverse(Arg, DefinedVars, State),
      %LastClause = lists:last(Clauses),
      CasesInfo = get(cases),
      put(cases,[{cerl_trees_:get_label(cerl:case_arg(Tree)),ArgVar,Clauses}|CasesInfo]),
      handle_clauses(Clauses, mk_var(Tree), ArgVar, DefinedVars,[cerl_trees_:get_label(Tree)], ArgLbl, State1);
    call ->
      handle_call(Tree, DefinedVars, State);
    'catch' ->
      %% XXX: Perhaps there is something to say about this.
      {State, mk_var(Tree),[cerl_trees_:get_label(Tree)]};
    cons ->
      Hd = cerl:cons_hd(Tree),
      Tl = cerl:cons_tl(Tree),
      {State1, [HdVar, TlVar],[HdLbl,TlLbl]} = traverse_list([Hd, Tl], DefinedVars, State),
      case cerl:is_literal(cerl:fold_literal(Tree)) of
		true ->
		  %% We do not need to do anything more here.
%		  io:format("\n\nTree: ~p\ncerl_trees_:get_label(Tree): ~w\nHdLbl: ~w\nTlLbl: ~w\n",
%		           [Tree,cerl_trees_:get_label(Tree),HdLbl,TlLbl]),
		  {State, t_cons(HdVar, TlVar),[cerl_trees_:get_label(Tree)|HdLbl++TlLbl]};
		false ->
		  ConsVar = mk_var(Tree),
		  ConsType = mk_fun_var(fun(Map) ->
					    t_cons(lookup_type(HdVar, Map),
						   lookup_type(TlVar, Map))
					end, [HdVar, TlVar]),
		  HdType = mk_fun_var(fun(Map) ->
					  Cons = lookup_type(ConsVar, Map),
					  case t_is_cons(Cons) of
					    false -> t_any();
					    true -> t_cons_hd(Cons)
					  end
				      end, [ConsVar]),
		  TlType = mk_fun_var(fun(Map) ->
					  Cons = lookup_type(ConsVar, Map),
					  case t_is_cons(Cons) of
					    false -> t_any();
					    true -> t_cons_tl(Cons)
					  end
				      end, [ConsVar]),
	      State2 = state__store_conj_lists_slicing([HdVar, TlVar, ConsVar], sub,
						   [HdType, TlType, ConsType],
						   [cerl_trees_:get_label(Tree)],
						   [HdLbl,TlLbl,[]],
						   State1),
		  {State2, ConsVar,[cerl_trees_:get_label(Tree)]}
      end;
    'fun' ->
      Body = cerl:fun_body(Tree),
      Vars = cerl:fun_vars(Tree),
      DefinedVars1 = add_def_list(Vars, [cerl_trees_:get_label(Tree)], DefinedVars),
      State0 = state__new_constraint_context_slicing(State),
      FunFailType =
		case state__prop_domain(cerl_trees:get_label(Tree), State0) of
		  error -> t_fun(length(Vars), t_none());
		  {ok, Dom} -> t_fun(Dom, t_none())
		end,
      TreeVar = mk_var(Tree),
      State2 =
		try
		  State1 = case state__add_prop_constrs(Tree, State0) of
			     not_called -> State0;
			     PropState -> PropState
			   end,
		  {BodyState, BodyVar,BodyLbl} = traverse(Body, DefinedVars1, State1),
		  state__store_conj_slicing(TreeVar, eq,
				    t_fun(mk_var_list(Vars), BodyVar), [cerl_trees_:get_label(Tree)|BodyLbl], BodyState)
		catch
		  throw:error ->
		    state__store_conj_slicing(TreeVar, eq, FunFailType, [cerl_trees_:get_label(Tree)], State0)
		end,
      Cs = state__cs(State2),
      Cs_slicing = state__cs_slicing(State2),
      State3 = state__store_constrs_slicing(TreeVar, Cs, Cs_slicing, State2),
      %State3 = state__store_constrs(TreeVar, Cs, State2),
      Ref = mk_constraint_ref(TreeVar, get_deps(Cs)),
      OldCs = state__cs(State),
      OldCs_slicing = state__cs_slicing(State),
      State4 = state__new_constraint_context_slicing(State3),
      State5_ = state__store_conj_list_slicing([OldCs_slicing, Ref], State4),
      State5 = state__store_conj_list([OldCs, Ref], State5_),
      State6 = state__store_fun_arity(Tree, State5),
      State7 = state__add_fun_to_scc(TreeVar, State6),
      {State7, TreeVar,[cerl_trees_:get_label(Tree)]};
    'let' ->
      Vars = cerl:let_vars(Tree),
      Arg = cerl:let_arg(Tree),
      Body = cerl:let_body(Tree),
      LblVars = [cerl_trees_:get_label(Var)||Var<-Vars],
      {State1, ArgVars,ArgLbl} = traverse(Arg, DefinedVars, State),
      State2 = state__store_conj_slicing(t_product(mk_var_list(Vars)), eq,
				 ArgVars, LblVars ++ ArgLbl, State1),
      DefinedVars1 = add_def_list(Vars, LblVars ++ ArgLbl, DefinedVars),
      traverse(Body, DefinedVars1, State2);
    letrec -> %JJJ no revisado
      Defs = cerl:letrec_defs(Tree),
      Body = cerl:letrec_body(Tree),
      Funs = [Fun || {_Var, Fun} <- Defs],
      Vars = [Var || {Var, _Fun} <- Defs],
      State1 = state__store_funs(Vars, Funs, State),
      Lbl = 
	      try
	        [cerl_trees_:get_label(Tree)]
	      catch
	      	{missing_label, _} -> []
	      end,
      DefinedVars1 = add_def_list(Vars, Lbl , DefinedVars),
      {State2, _,_} = traverse_list(Funs, DefinedVars1, State1),%JJJ Pending
      traverse(Body, DefinedVars1, State2);
    literal ->
      %% This is needed for finding records
      %io:format("Literal: ~p\n",[Tree]),
      case cerl:unfold_literal(Tree) of
		Tree ->
		  Type = t_from_term(cerl:concrete(Tree)),
		  NewType =
		    case erl_types:t_opaque_match_atom(Type, State#state.opaques) of
		      [Opaque] -> Opaque;
		      _ -> Type
		    end,
		  Lbl = 
		      try
		        [cerl_trees_:get_label(Tree)]
		      catch
		      	{missing_label, _} -> []
		      end,
		  {State, NewType,Lbl};
		NewTree_ -> 
		  FLbl = fun (Node) -> 
			    case cerl:get_ann(Node) of
			         [] -> cerl:set_ann(Node,cerl:get_ann(Tree));		
				 _ -> Node
			    end
		         end,
		  NewTree = cerl_trees_:map(FLbl,NewTree_),
		  traverse(NewTree, DefinedVars, State)
	      end;
    module ->
      Defs = cerl:module_defs(Tree),
      Funs = [Fun || {_Var, Fun} <- Defs],
      Vars = [Var || {Var, _Fun} <- Defs],
      DefinedVars1 = add_def_list(Vars, [cerl_trees_:get_label(Tree)], DefinedVars),
      State1 = state__store_funs(Vars, Funs, State),
      FoldFun = fun(Fun, AccState) ->
		    {S, _,_} = traverse(Fun, DefinedVars1,
				      state__new_constraint_context(AccState)),
		    S
		end,
      lists:foldl(FoldFun, State1, Funs);
    primop ->
      case cerl:atom_val(cerl:primop_name(Tree)) of
		match_fail -> throw(error);
		raise -> throw(error);
		bs_init_writable -> {State, t_from_term(<<>>),[cerl_trees_:get_label(Tree)]};
		Other -> erlang:error({'Unsupported primop', Other})
      end;
    'receive' ->
      Clauses = filter_match_fail(cerl:receive_clauses(Tree)),
      Timeout = cerl:receive_timeout(Tree),
      case (cerl:is_c_atom(Timeout) andalso
	    (cerl:atom_val(Timeout) =:= infinity)) of
	    % JJJ Pending en las dos llamadas a handle_clause la lista vacia
		true ->
		  handle_clauses(Clauses, mk_var(Tree), [], DefinedVars, [cerl_trees_:get_label(Tree)],[], State);
	 	false ->
		  Action = cerl:receive_action(Tree),
		  {State1, TimeoutVar,_} = traverse(Timeout, DefinedVars, State),
		  State2 = state__store_conj_slicing(TimeoutVar, sub, t_timeout(), [cerl_trees_:get_label(Tree)], State1),
		  handle_clauses(Clauses, mk_var(Tree), [], Action, DefinedVars, [cerl_trees_:get_label(Tree)],[], State2)
     end;
    seq ->
      Body = cerl:seq_body(Tree),
      Arg = cerl:seq_arg(Tree),
%      {State1, Type,Defs} = traverse(Body, DefinedVars, State),
%      {State2,_,_} = traverse(Arg, DefinedVars, State1),
%      {State2, Type,Defs};
      %OldCs = state__cs(State),
      %io:format("OldCs: ~p\n",[OldCs]),
      {State1, _,_} = traverse(Arg, DefinedVars, State),
      %NewCs = state__cs(State1),
      %io:format("NewCs: ~p\n",[NewCs]),
      traverse(Body, DefinedVars, State1);
    'try' ->
      handle_try(Tree, DefinedVars, State);
    tuple ->
      Elements = cerl:tuple_es(Tree),
      {State1, EVars,_} = traverse_list(Elements, DefinedVars, State), %JJJ Pending
      {State2, TupleType} =
		case cerl:is_literal(cerl:fold_literal(Tree)) of
		  true ->
		    %% We do not need to do anything more here.
		    {State, t_tuple(EVars)};
		  false ->
		    %% We have the same basic problem as in products, but we want to
		    %% make sure that everything that can be used as tags for the
		    %% disjoint unions stays in the tuple.
		    Fun = fun(Var, AccState) ->
			      case t_has_var(Var) of
				true ->
				  {AccState1, NewVar} = state__mk_var(AccState),
				  {NewVar,
				   state__store_conj_slicing(Var, eq, NewVar, [cerl_trees_:get_label(Tree)], AccState1)};
				false ->
				  {Var, AccState}
			      end
			  end,
		    {NewEvars, TmpState} = lists:mapfoldl(Fun, State1, EVars),
		    {TmpState, t_tuple(NewEvars)}
		end,
      case Elements of
		[Tag|Fields] ->
		  case cerl:is_c_atom(Tag) of
		    true ->
		      %% Check if an opaque term is constructed.
		      case t_opaque_match_record(TupleType, State#state.opaques) of
				[Opaque] ->
				  OpStruct = t_opaque_matching_structure(TupleType, Opaque),
				  State3 = state__store_conj_slicing(TupleType, sub, OpStruct, [cerl_trees_:get_label(Tree)], State2),
				  {State3, Opaque,[cerl_trees_:get_label(Tree)]};
				%% Check if a record is constructed.
				_ ->
				  Arity = length(Fields),
				  case state__lookup_record(State2, cerl:atom_val(Tag), Arity) of
				    error -> {State2, TupleType,[cerl_trees_:get_label(Tree)]};
				    {ok, RecType} ->
				      State3 = state__store_conj_slicing(TupleType, sub, RecType, [cerl_trees_:get_label(Tree)], State2),
				      {State3, TupleType,[cerl_trees_:get_label(Tree)]}
				  end
		      end;
		    false -> {State2, TupleType,[cerl_trees_:get_label(Tree)]}
		  end;
		[] -> {State2, TupleType,[cerl_trees_:get_label(Tree)]}
      end;
    values -> % JJJ Pending
      %% We can get into trouble when unifying products that have the
      %% same element appearing several times. Handle these cases by
      %% introducing fresh variables and constraining them to be equal
      %% to the original ones. This is similar to what happens in
      %% pattern matching where the matching is done on fresh
      %% variables and guards assert that the matching is correct.
      Elements = cerl:values_es(Tree),
      % JJJ Pending
      {State1, EVars, _ } = traverse_list(Elements, DefinedVars, State),
      Arity = length(EVars),
      Unique = length(ordsets:from_list(EVars)),
      case Arity =:= Unique of
		true -> {State1, t_product(EVars),[cerl_trees_:get_label(Tree)]};
		false ->
		  {State2, Vars} = state__mk_vars(Arity, State1),
		  State3 = state__store_conj_lists_slicing(Vars, eq, EVars, [cerl_trees_:get_label(Tree)],[], State2),
		  {State3, t_product(Vars),[cerl_trees_:get_label(Tree)]}
      end;
    var ->
      case is_def(Tree, DefinedVars) of
		%{true,Lbl} -> {State, mk_var(Tree),[cerl_trees_:get_label(Tree)|Lbl]};
		{true,_} -> {State, mk_var(Tree),[cerl_trees_:get_label(Tree)]};
		{false,[]} ->
		  %% If we are analyzing SCCs this can be a function variable.
		  case state__lookup_undef_var(Tree, State) of
		    error -> erlang:error({'Undefined variable', Tree});
		    {ok, Type} ->
		      {State1, NewVar} = state__mk_var(State),
		      {state__store_conj_slicing(NewVar, sub, Type, [cerl_trees_:get_label(Tree)], State1),
		       NewVar,[cerl_trees_:get_label(Tree)]}
		  end
      end;
    Other ->
      erlang:error({'Unsupported type', Other})
  end.

traverse_list(Trees, DefinedVars, State) ->
  traverse_list(Trees, DefinedVars, State, [],[]).

traverse_list([Tree|Tail], DefinedVars, State, Acc,Acc2) ->
  {State1, Var,Lbl} = traverse(Tree, DefinedVars, State),
  traverse_list(Tail, DefinedVars, State1, [Var|Acc], [Lbl|Acc2]);
traverse_list([], _DefinedVars, State, Acc, Acc2) ->
  {State, lists:reverse(Acc), lists:reverse(Acc2)}.

add_def(Var, Lbl, {Set,Dict}) ->
  {sets:add_element(cerl_trees:get_label(Var), Set),
   dict:append(cerl_trees:get_label(Var),Lbl,Dict)}. %%JJJ Esta bien? A la variable original le correponden las etiquetas Lbl

add_def_list([H|T], Lbl, DefinenVars) ->
  add_def_list(T, Lbl, add_def(H, Lbl, DefinenVars));
add_def_list([], _Lbl, DefinenVars) ->
  DefinenVars.

add_def_from_tree(T, Lbl, DefinedVars) ->
  Vars = cerl_trees:fold(fun(X, Acc) ->
			     case cerl:is_c_var(X) of
			       true -> [X|Acc];
			       false -> Acc
			     end
			 end, [], T),
  add_def_list(Vars, Lbl, DefinedVars).

add_def_from_tree_list([H|T], [Lbl|Lbls], DefinedVars) ->
  add_def_from_tree_list(T, Lbls, add_def_from_tree(H, Lbl, DefinedVars));
add_def_from_tree_list([], [], DefinedVars) ->
  DefinedVars.

is_def(Var, {Set,Dict}) ->
  case sets:is_element(cerl_trees:get_label(Var), Set) of
       true -> [Lbl]=dict:fetch(cerl_trees:get_label(Var),Dict),{true,Lbl} ;
       false -> {false,[]}
  end.

%%----------------------------------------
%% Try
%%

handle_try(Tree, DefinedVars, State) ->
  Arg = cerl:try_arg(Tree),
  Vars = cerl:try_vars(Tree),
  EVars = cerl:try_evars(Tree),
  Body = cerl:try_body(Tree),
  Handler = cerl:try_handler(Tree),
  State1 = state__new_constraint_context(State),
  {ArgBodyState, BodyVar} =
    try
      {State2, ArgVar,_} = traverse(Arg, DefinedVars, State1),
      DefinedVars1 = add_def_list(Vars, [cerl_trees_:get_label(Tree)], DefinedVars),
      {State3, BodyVar1,_} = traverse(Body, DefinedVars1, State2),
      State4 = state__store_conj_slicing(t_product(mk_var_list(Vars)), eq, ArgVar, [cerl_trees_:get_label(Tree)], 
				 State3),
      {State4, BodyVar1}
    catch
      throw:error ->
	{State1, t_none()}
    end,
  State6 = state__new_constraint_context(ArgBodyState),
  {HandlerState, HandlerVar} =
    try
      DefinedVars2 = add_def_list([X || X <- EVars, cerl:is_c_var(X)],
				  [cerl_trees_:get_label(Tree)], DefinedVars),
      traverse(Handler, DefinedVars2, State6)
    catch
      throw:error ->
	{State6, t_none()}
    end,
  ArgBodyCs = state__cs(ArgBodyState),
  HandlerCs = state__cs(HandlerState),
  TreeVar = mk_var(Tree),
  OldCs = state__cs(State),
  case state__is_in_guard(State) of
    true ->
      Conj1 = mk_conj_constraint_list([ArgBodyCs,
				       mk_constraint(BodyVar, eq, TreeVar)]),
      Disj = mk_disj_constraint_list([Conj1,
				      mk_constraint(HandlerVar, eq, TreeVar)]),
      NewState1 = state__new_constraint_context(HandlerState),
      %JJJ FALTA SLICING
      Conj2 = mk_conj_constraint_list([OldCs, Disj]),
      NewState2 = state__store_conj(Conj2, NewState1), 
      {NewState2, TreeVar,[cerl_trees_:get_label(Tree)]};
    false ->
      {NewCs, ReturnVar} =
		case {t_is_none(BodyVar), t_is_none(HandlerVar)} of
		  {false, false} ->
		    Conj1 =
		      mk_conj_constraint_list([ArgBodyCs,
					       mk_constraint(TreeVar, eq, BodyVar)]),
		    Conj2 =
		      mk_conj_constraint_list([HandlerCs,
					       mk_constraint(TreeVar, eq, HandlerVar)]),
		    Disj = mk_disj_constraint_list([Conj1, Conj2]),
		    {Disj, TreeVar};
		  {false, true} ->
		    {mk_conj_constraint_list([ArgBodyCs,
					      mk_constraint(TreeVar, eq, BodyVar)]),
		     BodyVar};
		  {true, false} ->
		    {mk_conj_constraint_list([HandlerCs,
					      mk_constraint(TreeVar, eq, HandlerVar)]),
		     HandlerVar};
		  {true, true} ->
		    ?debug("Throw failed\n", []),
		    throw(error)
		end,
	  %JJJ FALTA SLICING
      Conj = mk_conj_constraint_list([OldCs, NewCs]),
      NewState1 = state__new_constraint_context(HandlerState),
      NewState2 = state__store_conj(Conj, NewState1),
      {NewState2, ReturnVar,[cerl_trees_:get_label(Tree)]}
  end.

%%----------------------------------------
%% Call
%%

handle_call(Call, DefinedVars, State) ->
  Args = cerl:call_args(Call),
  Mod = cerl:call_module(Call),
  Fun = cerl:call_name(Call),
  Dst = mk_var(Call),
  case cerl:is_c_atom(Mod) andalso cerl:is_c_atom(Fun) of
    true ->
      M = cerl:atom_val(Mod),
      F = cerl:atom_val(Fun),
      A = length(Args),
      MFA = {M, F, A},
      {State1, ArgVars,LblArgs} = traverse_list(Args, DefinedVars, State), %JJJ2
      %JJJ FALTA SLICING
      case state__lookup_rec_var_in_scope(MFA, State) of
		error ->
		  case get_bif_constr(MFA, Dst, ArgVars, State1) of
		    none ->
		      {get_plt_constr(MFA, Dst, ArgVars, State1), Dst,[cerl_trees_:get_label(Call)]};
		    C ->
		      {constraint_list,conj,ListCtrs,Deps,Id}=C,
		      LblModFun = [cerl_trees_:get_label(cerl:call_module(Call)),
				   cerl_trees_:get_label(cerl:call_name(Call))],
		      LblCall = [cerl_trees_:get_label(Call)],
		      CS = 
%		       	{erlang, '++', 2}
%			(te primer la del call, despres 1 del 1er, 1 del 2on, i altra vola 1 del 1er i del 2on)
%			{erlang, 'or', 2}
%			el ultim elemnt es una disjuncio de la mateixa forma
%			{erlang, element, 2}
%			pot ser igual o tindre antes dels args una restriccio adicional del call
		       case lists:member(MFA,[{erlang, '++', 2},{erlang, 'or', 2},
		                              {erlang, element, 2},{erlang, get_module_info, 2},
		                              {erlang, get_module_info, 1}]) of
		            true -> {constraint_list_slicing,conj,
				          [{constraint_slicing,Ctr,LblCall++LblModFun++lists:flatten(LblArgs)}
				           ||Ctr<-ListCtrs],
				          Deps,Id};
			     false -> %io:format("MFA: ~p\nListCtrs: ~p\nLblArgs: ~w\n",[MFA,ListCtrs,LblArgs]),
			              {constraint_list_slicing,conj,
			               build_constraint_slicing_bif(ListCtrs,LblModFun,LblCall,LblArgs),
			               Deps,Id}
		      end,
		      State2=state__store_conj(C, State1),
		      {state__store_conj_slicing(CS, State2), Dst,[cerl_trees_:get_label(Call)]}
		  end;
		{ok, Var} ->
		  %% This is part of the SCC currently analyzed.
		  %% Intercept and change this to an apply instead.
		  ?debug("Found the call to ~w\n", [MFA]),
		  Label = cerl_trees:get_label(Call),
		  LabelSlicing = cerl_trees_:get_label(Call),
		  Apply = cerl:ann_c_apply([{label, Label},{label_slicing,LabelSlicing}], Var, Args),
		  traverse(Apply, DefinedVars, State)
	   end;
    false ->
      {State1, MF,_} = traverse_list([Mod, Fun], DefinedVars, State),
      {state__store_conj_lists_slicing(MF, sub, [t_module(), t_atom()], [cerl_trees_:get_label(Call)], [], State1), 
       Dst,[cerl_trees_:get_label(Call)]}
  end.
  
build_constraint_slicing_bif([C|Cs],LblModFun,LblCall,LblArgs)->
   [{constraint_slicing,C,LblCall++LblModFun}|build_constraint_slicing_bif(Cs,LblCall,LblArgs)].


build_constraint_slicing_bif([C|Cs],LblCall,[LblArg|LblArgs])->
   [{constraint_slicing,C,LblCall++LblArg}|build_constraint_slicing_bif(Cs,LblCall,LblArgs)];
build_constraint_slicing_bif([],_,[]) -> [].

get_plt_constr(MFA, Dst, ArgVars, State) ->
  Plt = state__plt(State),
  PltRes = dialyzer_plt:lookup(Plt, MFA),
  Opaques = State#state.opaques,
  Module = State#state.module,
  {FunModule, _, _} = MFA,
  case dialyzer_plt:lookup_contract(Plt, MFA) of
    none ->
      case PltRes of
	none -> State;
	{value, {PltRetType, PltArgTypes}} ->
	  state__store_conj_lists_slicing([Dst|ArgVars], sub,
				  [PltRetType|PltArgTypes], [], [[] || _ <- [PltRetType|PltArgTypes] ], State)
      end;
    {value, #contract{args = GenArgs} = C} ->
      {RetType, ArgCs,Lbl} =
	case PltRes of
	  none ->
	    {mk_fun_var(fun(Map) ->
			    ArgTypes = lookup_type_list(ArgVars, Map),
			    dialyzer_contracts:get_contract_return(C, ArgTypes)
			end, ArgVars), GenArgs,[]};
	  {value, {PltRetType, PltArgTypes}} ->
	    %% Need to combine the contract with the success typing.
	    {mk_fun_var(
	       fun(Map) ->
		   ArgTypes0 = lookup_type_list(ArgVars, Map),
		   ArgTypes = case FunModule =:= Module of
				false ->
				  List = lists:zip(PltArgTypes, ArgTypes0),
				  [erl_types:t_unopaque_on_mismatch(T1, T2, Opaques)
				   || {T1, T2} <- List];
				true -> ArgTypes0
			      end,
		   CRet = dialyzer_contracts:get_contract_return(C, ArgTypes),
		   t_inf(CRet, PltRetType, opaque)
	       end, ArgVars),
	     [t_inf(X, Y, opaque) || {X, Y} <- lists:zip(GenArgs, PltArgTypes)],[]}
	end,
      state__store_conj_lists_slicing(ArgVars++[Dst], sub, ArgCs++[RetType], [], Lbl, State)
  end.

filter_match_fail([Clause] = Cls) ->
  Body = cerl:clause_body(Clause),
  case cerl:type(Body) of
    primop ->
      case cerl:atom_val(cerl:primop_name(Body)) of
	match_fail -> [];
	raise -> [];
	_ -> Cls
      end;
    _ -> Cls
  end;
filter_match_fail([H|T]) ->
  [H|filter_match_fail(T)];
filter_match_fail([]) ->
  %% This can actually happen, for example in
  %%      receive after 1 -> ok end
  [].

%% If there is a significant number of clauses, we cannot apply the
%% list subtraction scheme since it causes the analysis to be too
%% slow. Typically, this only affects automatically generated files.
%% The dataflow analysis doesn't suffer from this, so we will get some
%% information anyway.
-define(MAX_NOF_CLAUSES, 15).

handle_clauses(Clauses, TopVar, Arg, DefinedVars,Lbl, Arglbl, State) ->
  handle_clauses(Clauses, TopVar, Arg, none, DefinedVars,Lbl, Arglbl, State).

handle_clauses([], _, _, Action, DefinedVars, _, _, State) when Action =/= none ->
  %% Can happen when a receive has no clauses, see filter_match_fail.
  traverse(Action, DefinedVars, State);
handle_clauses(Clauses, TopVar, Arg, Action, DefinedVars,Lbl, ArgLbl, State) ->
  SubtrTypeList =
    if length(Clauses) > ?MAX_NOF_CLAUSES -> overflow;
       true -> []
    end,
  %io:format("State.cs: ~p\nState.cs_slicing: ~p\n",[State#state.cs,State#state.cs_slicing]),
  {State1, CList,CListSlicing} = handle_clauses_1(Clauses, TopVar, Arg, DefinedVars,
				     State, SubtrTypeList,Lbl, ArgLbl, [],[]),
  %io:format("CList: ~p\nCListSlicing: ~p\n",[CList,CListSlicing]),
  {NewCs, NewState} =
    case Action of
      none ->
		if CList =:= [] -> throw(error);
		   true -> {CList, State1}
		end;
      _ ->
		try
		  {State2, ActionVar,_} = traverse(Action, DefinedVars, State1), %JJJ PENDING
		  TmpC = mk_constraint(TopVar, eq, ActionVar),
		  ActionCs = mk_conj_constraint_list([state__cs(State2),TmpC]),%JJJ PENDING
		  {[ActionCs|CList], State2}
		catch
		  throw:error ->
		    if CList =:= [] -> throw(error);
		       true -> {CList, State1}
		    end
		end
    end,
  OldCs = state__cs(State),
  OldCsSlicing = state__cs_slicing(State),
  NewCList = mk_disj_constraint_list(NewCs),
  %io:format("OldCs: ~p\n",[OldCs]),
  NewCListSlicing = mk_disj_constraint_list_slicing(CListSlicing),
  FinalState_ = state__new_constraint_context(NewState),
  FinalState = state__new_constraint_context_slicing(FinalState_),
  %io:format("NewCList: ~p\n",[NewCList]),
  FinalState2 = state__store_conj_list([OldCs, NewCList], FinalState),
  %io:format("NewCs: ~p\n",[state__cs(FinalState2)]),
  {state__store_conj_list_slicing([OldCsSlicing, NewCListSlicing], FinalState2), TopVar,Lbl}.

handle_clauses_1([Clause|Tail], TopVar, Arg, DefinedVars,
		 State, SubtrTypes, Lbl, ArgLbl, Acc, AccSlicing) ->
  State0 = state__new_constraint_context_slicing(State),
  Pats = cerl:clause_pats(Clause),
  Guard = cerl:clause_guard(Clause),
  Body = cerl:clause_body(Clause),
  NewSubtrTypes =
    case SubtrTypes =:= overflow of
      true -> overflow;
      false ->
		ordsets:add_element(get_safe_underapprox(Pats, Guard), SubtrTypes)
    end,
  try
    %io:format("entra: ~p\n",[cerl:get_ann(Clause)]),
    case lists:member(compiler_generated, cerl:get_ann(Clause)) of
         true ->
            handle_clauses_1(Tail, TopVar, Arg, DefinedVars,
		             State, NewSubtrTypes, Lbl, ArgLbl,  Acc, AccSlicing);
         false ->
            PatLbl_=[[cerl_trees_:get_label(P)] || P <- Pats],
	    DefinedVars1 = add_def_from_tree_list(Pats, PatLbl_, DefinedVars),
	    State1 = state__set_in_match(State0, true),
	    {State2, PatVars,PatLbl} = traverse_list(Pats, DefinedVars1, State1),
	    State3 =
	      case Arg =:= [] of
		true -> State2;
	        false ->
	          %io:format("CASE: ~w\n",[{PatLbl,ArgLbl}]),
	          S = state__store_conj_slicing(Arg, eq, t_product(PatVars),lists:flatten(PatLbl)++ArgLbl, State2),
		  case SubtrTypes =:= overflow of
		    true -> S;
		    false ->
		      SubtrPatVar = mk_fun_var(fun(Map) ->
						   TmpType = lookup_type(Arg, Map),
						   t_subtract_list(TmpType, SubtrTypes)
					       end, [Arg]),
		      state__store_conj_slicing(Arg, sub, SubtrPatVar, lists:flatten(PatLbl)++ArgLbl, S)
		  end
	      end,
	    State4 = handle_guard(Guard, DefinedVars1, State3),
	    {State5, BodyVar,BodyLbl} = traverse(Body, DefinedVars1,
					 state__set_in_match(State4, false)),
	    State6 = state__store_conj_slicing(TopVar, eq, BodyVar,Lbl++BodyLbl, State5),
	    Cs = state__cs(State6),
	    CsSlicing = state__cs_slicing(State6),
	    handle_clauses_1(Tail, TopVar, Arg, DefinedVars, State6,
			     NewSubtrTypes, Lbl, ArgLbl, [Cs|Acc], [CsSlicing|AccSlicing])
      end
  catch
    throw:error ->
      handle_clauses_1(Tail, TopVar, Arg, DefinedVars,
		       State, NewSubtrTypes, Lbl, ArgLbl,  Acc, AccSlicing)
  end;
handle_clauses_1([], _TopVar, _Arg, _DefinedVars, State, _SubtrType, _Lbl, _ArgLbl, Acc, AccSlicing) ->
  {state__new_constraint_context(State), Acc, AccSlicing}.

-spec get_safe_underapprox([cerl:c_values()], cerl:cerl()) -> erl_types:erl_type().

get_safe_underapprox(Pats, Guard) ->
  try
    Map1 = cerl_trees:fold(fun(X, Acc) ->
			       case cerl:is_c_var(X) of
				 true ->
				   dict:store(cerl_trees:get_label(X), t_any(),
					      Acc);
				 false -> Acc
			       end
			   end, dict:new(), cerl:c_values(Pats)),
    {Type, Map2} = get_underapprox_from_guard(Guard, Map1),
    Map3 = case t_is_none(t_inf(t_from_term(true), Type)) of
	     true -> throw(dont_know);
	     false ->
	       case cerl:is_c_var(Guard) of
		 false -> Map2;
		 true ->
		   dict:store(cerl_trees:get_label(Guard),
			      t_from_term(true), Map2)
	       end
	   end,
    {Ts, _Map4} = get_safe_underapprox_1(Pats, [], Map3),
    t_product(Ts)
  catch
    throw:dont_know -> t_none()
  end.

get_underapprox_from_guard(Tree, Map) ->
  True = t_from_term(true),
  case cerl:type(Tree) of
    call ->
      case {cerl:concrete(cerl:call_module(Tree)),
	    cerl:concrete(cerl:call_name(Tree)),
	    length(cerl:call_args(Tree))} of
	{erlang, is_function, 2} ->
	  [Fun, Arity] = cerl:call_args(Tree),
	  case cerl:is_c_int(Arity) of
	    false -> throw(dont_know);
	    true ->
	      {FunType, Map1} = get_underapprox_from_guard(Fun, Map),
	      Inf = t_inf(FunType, t_fun(cerl:int_val(Arity), t_any())),
	      case t_is_none(Inf) of
		true -> throw(dont_know);
		false ->
		  {True, dict:store(cerl_trees:get_label(Fun), Inf, Map1)}
	      end
	  end;
	MFA ->
	  case get_type_test(MFA) of
	    {ok, Type} ->
	      [Arg] = cerl:call_args(Tree),
	      {ArgType, Map1} = get_underapprox_from_guard(Arg, Map),
	      Inf = t_inf(Type, ArgType),
	      case t_is_none(Inf) of
		true -> throw(dont_know);
		false ->
		  case cerl:is_literal(Arg) of
		    true -> {True, Map1};
		    false ->
		      {True, dict:store(cerl_trees:get_label(Arg), Inf, Map1)}
		  end
	      end;
	    error ->
	      case MFA of
		{erlang, '=:=', 2} -> throw(dont_know);
		{erlang, '==', 2} -> throw(dont_know);
		{erlang, 'and', 2} ->
		  [Arg1, Arg2] = cerl:call_args(Tree),
		  case ((cerl:is_c_var(Arg1) orelse cerl:is_literal(Arg1))
			andalso
			(cerl:is_c_var(Arg2) orelse cerl:is_literal(Arg2))) of
		    true ->
		      {Arg1Type, _} = get_underapprox_from_guard(Arg1, Map),
		      {Arg2Type, _} = get_underapprox_from_guard(Arg2, Map),
		      case (t_is_equal(True, Arg1Type) andalso
			    t_is_equal(True, Arg2Type)) of
			true -> {True, Map};
			false -> throw(dont_know)
		      end;
		    false ->
		      throw(dont_know)
		  end;
		{erlang, 'or', 2} -> throw(dont_know);
		_ -> throw(dont_know)
	      end
	  end
      end;
    var ->
      Type =
	case dict:find(cerl_trees:get_label(Tree), Map) of
	  error -> throw(dont_know);
	  {ok, T} -> T
	end,
      {Type, Map};
    literal ->
      case cerl:unfold_literal(Tree) of
	Tree ->
	  Type =
	    case cerl:concrete(Tree) of
	      Int when is_integer(Int) -> t_from_term(Int);
	      Atom when is_atom(Atom) -> t_from_term(Atom);
	      _Other -> throw(dont_know)
	    end,
	  {Type, Map};
	OtherTree ->
	  get_underapprox_from_guard(OtherTree, Map)
      end;
    _ ->
      throw(dont_know)
  end.

%%
%% The guard test {erlang, is_function, 2} is handled specially by the
%% function get_underapprox_from_guard/2
%%
get_type_test({erlang, is_atom, 1}) ->      {ok, t_atom()};
get_type_test({erlang, is_boolean, 1}) ->   {ok, t_boolean()};
get_type_test({erlang, is_binary, 1}) ->    {ok, t_binary()};
get_type_test({erlang, is_bitstring, 1}) -> {ok, t_bitstr()};
get_type_test({erlang, is_float, 1}) ->     {ok, t_float()};
get_type_test({erlang, is_function, 1}) ->  {ok, t_fun()};
get_type_test({erlang, is_integer, 1}) ->   {ok, t_integer()};
get_type_test({erlang, is_list, 1}) ->      {ok, t_list()};
get_type_test({erlang, is_number, 1}) ->    {ok, t_number()};
get_type_test({erlang, is_pid, 1}) ->       {ok, t_pid()};
get_type_test({erlang, is_port, 1}) ->      {ok, t_port()};
%% get_type_test({erlang, is_record, 2}) ->    {ok, t_tuple()};
%% get_type_test({erlang, is_record, 3}) ->    {ok, t_tuple()};
get_type_test({erlang, is_reference, 1}) -> {ok, t_reference()};
get_type_test({erlang, is_tuple, 1}) ->     {ok, t_tuple()};
get_type_test({M, F, A}) when is_atom(M), is_atom(F), is_integer(A) -> error.

bitstr_constr(SizeType, UnitVal) ->
  fun(Map) ->
      TmpSizeType = lookup_type(SizeType, Map),
      case t_is_subtype(TmpSizeType, t_non_neg_integer()) of
	true ->
	  case t_number_vals(TmpSizeType) of
	    [OneSize] -> t_bitstr(0, OneSize * UnitVal);
	    _ ->
	      MinSize = erl_types:number_min(TmpSizeType),
	      t_bitstr(UnitVal, MinSize * UnitVal)
	  end;
	false ->
	  t_bitstr(UnitVal, 0)
      end
  end.

bitstr_val_constr(SizeType, UnitVal, Flags) ->
  fun(Map) ->
      TmpSizeType = lookup_type(SizeType, Map),
      case t_is_subtype(TmpSizeType, t_non_neg_integer()) of
	true ->
	  case erl_types:number_max(TmpSizeType) of
	    N when is_integer(N), N < 128 -> %% Avoid illegal arithmetic
	      TotalSizeVal = N * UnitVal,
	      {RangeMin, RangeMax} =
		case lists:member(signed, Flags) of
		  true -> {-(1 bsl (TotalSizeVal - 1)),
			   1 bsl (TotalSizeVal - 1) - 1};
		  false -> {0, 1 bsl TotalSizeVal - 1}
		end,
	      t_from_range(RangeMin, RangeMax);
	    _ ->
	      t_integer()
	  end;
	false ->
	  t_integer()
      end
  end.

get_safe_underapprox_1([Pat|Left], Acc, Map) ->
  case cerl:type(Pat) of
    alias ->
      APat = cerl:alias_pat(Pat),
      AVar = cerl:alias_var(Pat),
      {[VarType], Map1} = get_safe_underapprox_1([AVar], [], Map),
      {[PatType], Map2} = get_safe_underapprox_1([APat], [], Map1),
      Inf = t_inf(VarType, PatType),
      case t_is_none(Inf) of
	true -> throw(dont_know);
	false ->
	  Map3 = dict:store(cerl_trees:get_label(AVar), Inf, Map2),
	  get_safe_underapprox_1(Left, [Inf|Acc], Map3)
      end;
    binary ->
      %% TODO: Can maybe do something here
      throw(dont_know);
    cons ->
      {[Hd, Tl], Map1} =
	get_safe_underapprox_1([cerl:cons_hd(Pat), cerl:cons_tl(Pat)], [], Map),
      case t_is_any(Tl) of
	true -> get_safe_underapprox_1(Left, [t_nonempty_list(Hd)|Acc], Map1);
	false -> throw(dont_know)
      end;
    literal ->
      case cerl:unfold_literal(Pat) of
	Pat ->
	  Type =
	    case cerl:concrete(Pat) of
	      Int when is_integer(Int) -> t_from_term(Int);
	      Atom when is_atom(Atom) -> t_from_term(Atom);
	      [] -> t_from_term([]);
	      _Other -> throw(dont_know)
	    end,
	  get_safe_underapprox_1(Left, [Type|Acc], Map);
	OtherPat ->
	  get_safe_underapprox_1([OtherPat|Left], Acc, Map)
      end;
    tuple ->
      Es = cerl:tuple_es(Pat),
      {Ts, Map1} = get_safe_underapprox_1(Es, [], Map),
      Type = t_tuple(Ts),
      get_safe_underapprox_1(Left, [Type|Acc], Map1);
    values ->
      Es = cerl:values_es(Pat),
      {Ts, Map1} = get_safe_underapprox_1(Es, [], Map),
      Type = t_product(Ts),
      get_safe_underapprox_1(Left, [Type|Acc], Map1);
    var ->
      case dict:find(cerl_trees:get_label(Pat), Map) of
	error -> throw(dont_know);
	{ok, VarType} -> get_safe_underapprox_1(Left, [VarType|Acc], Map)
      end
  end;
get_safe_underapprox_1([], Acc, Map) ->
  {lists:reverse(Acc), Map}.

%%----------------------------------------
%% Guards
%%

handle_guard(Guard, DefinedVars, State) ->
  True = t_from_term(true),
  State1 = state__set_in_guard(State, true),
  State2 = state__new_constraint_context_slicing(State1),
  {State3, Return,LblGuards} = traverse(Guard, DefinedVars, State2),
  State4 = state__store_conj_slicing(Return, eq, True, LblGuards, State3),
  Cs = state__cs(State4),
  CsSlicing = state__cs_slicing(State4),
  NewCs = mk_disj_norm_form(Cs),
  NewCsSlicing = mk_disj_norm_form_slicing(CsSlicing),
  OldCs = state__cs(State),
  OldCsSlicing = state__cs_slicing(State),
  State5 = state__set_in_guard(State4, state__is_in_guard(State)),
  State6_ = state__new_constraint_context(State5),
  State6 = state__new_constraint_context_slicing(State6_),
  State7 = state__store_conj(mk_conj_constraint_list([OldCs, NewCs]), State6),
  state__store_conj_slicing(mk_conj_constraint_list_slicing([OldCsSlicing, NewCsSlicing]), State7).

%%=============================================================================
%%
%%  BIF constraints
%%
%%=============================================================================

get_bif_constr({erlang, Op, 2}, Dst, Args = [Arg1, Arg2], _State)
  when Op =:= '+'; Op =:= '-'; Op =:= '*' ->
  ReturnType = mk_fun_var(fun(Map) ->
			      TmpArgTypes = lookup_type_list(Args, Map),
			      erl_bif_types:type(erlang, Op, 2, TmpArgTypes)
			  end, Args),
  ArgFun =
    fun(A, Pos) ->
	F =
	  fun(Map) ->
	      DstType = lookup_type(Dst, Map),
	      AType = lookup_type(A, Map),
	      case t_is_integer(DstType) of
		true ->
		  case t_is_integer(AType) of
		    true ->
		      eval_inv_arith(Op, Pos, DstType, AType);
		    false  ->
		      %% This must be temporary.
		      t_integer()
		  end;
		false ->
		  case t_is_float(DstType) of
		    true ->
		      case t_is_integer(AType) of
			true -> t_float();
			false -> t_number()
		      end;
		    false ->
		      t_number()
		  end
	      end
	  end,
	mk_fun_var(F, [Dst, A])
    end,
  Arg1FunVar = ArgFun(Arg2, 2),
  Arg2FunVar = ArgFun(Arg1, 1),
  mk_conj_constraint_list([mk_constraint(Dst, sub, ReturnType ),
			   mk_constraint(Arg1, sub, Arg1FunVar),
			   mk_constraint(Arg2, sub, Arg2FunVar)]);
get_bif_constr({erlang, Op, 2}, Dst, [Arg1, Arg2] = Args, _State)
  when Op =:= '<'; Op =:= '=<'; Op =:= '>'; Op =:= '>=' ->
  ArgFun =
    fun(LocalArg1, LocalArg2, LocalOp) ->
	fun(Map) ->
	    DstType = lookup_type(Dst, Map),
	    IsTrue = t_is_atom(true, DstType),
	    IsFalse = t_is_atom(false, DstType),
	    case IsTrue orelse IsFalse of
	      true ->
		Arg1Type = lookup_type(LocalArg1, Map),
		Arg2Type = lookup_type(LocalArg2, Map),
		case t_is_integer(Arg1Type) andalso t_is_integer(Arg2Type) of
		  true ->
		    Max1 = erl_types:number_max(Arg1Type),
		    Min1 = erl_types:number_min(Arg1Type),
		    Max2 = erl_types:number_max(Arg2Type),
		    Min2 = erl_types:number_min(Arg2Type),
		    case LocalOp of
		      '=<' ->
			if IsTrue  -> t_from_range(Min1, Max2);
			   IsFalse -> t_from_range(range_inc(Min2), Max1)
			end;
		      '<'  ->
			if IsTrue  -> t_from_range(Min1, range_dec(Max2));
			   IsFalse -> t_from_range(Min2, Max1)
			end;
		      '>=' ->
			if IsTrue  -> t_from_range(Min2, Max1);
			   IsFalse -> t_from_range(Min1, range_dec(Max2))
			end;
		      '>'  ->
			if IsTrue  -> t_from_range(range_inc(Min2), Max1);
			   IsFalse -> t_from_range(Min1, Max2)
			end
		    end;
		  false -> t_any()
		end;
	      false -> t_any()
	    end
	end
    end,
  {Arg1Fun, Arg2Fun} =
    case Op of
      '<'  -> {ArgFun(Arg1, Arg2, '<'),  ArgFun(Arg2, Arg1, '>=')};
      '=<' -> {ArgFun(Arg1, Arg2, '=<'), ArgFun(Arg2, Arg1, '>=')};
      '>'  -> {ArgFun(Arg1, Arg2, '>'),  ArgFun(Arg2, Arg1, '<')};
      '>=' -> {ArgFun(Arg1, Arg2, '>='), ArgFun(Arg2, Arg1, '=<')}
    end,
  DstArgs = [Dst, Arg1, Arg2],
  Arg1Var = mk_fun_var(Arg1Fun, DstArgs),
  Arg2Var = mk_fun_var(Arg2Fun, DstArgs),
  DstVar = mk_fun_var(fun(Map) ->
			  TmpArgTypes = lookup_type_list(Args, Map),
			  erl_bif_types:type(erlang, Op, 2, TmpArgTypes)
		      end, Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstVar),
			   mk_constraint(Arg1, sub, Arg1Var),
			   mk_constraint(Arg2, sub, Arg2Var)]);
get_bif_constr({erlang, '++', 2}, Dst, [Hd, Tl] = Args, _State) ->
  HdFun = fun(Map) ->
	      DstType = lookup_type(Dst, Map),
	      case t_is_cons(DstType) of
		true -> t_list(t_cons_hd(DstType));
		false ->
		  case t_is_list(DstType) of
		    true ->
		      case t_is_nil(DstType) of
			true -> DstType;
			false -> t_list(t_list_elements(DstType))
		      end;
		    false -> t_list()
 		  end
	      end
	  end,
  TlFun = fun(Map) ->
	      DstType = lookup_type(Dst, Map),
	      case t_is_cons(DstType) of
		true -> t_sup(t_cons_tl(DstType), DstType);
		false ->
		  case t_is_list(DstType) of
		    true ->
		      case t_is_nil(DstType) of
			true -> DstType;
			false -> t_list(t_list_elements(DstType))
		      end;
		    false -> t_any()
		  end
	      end
	  end,
  DstL = [Dst],
  HdVar = mk_fun_var(HdFun, DstL),
  TlVar = mk_fun_var(TlFun, DstL),
  ArgTypes = erl_bif_types:arg_types(erlang, '++', 2),
  ReturnType = mk_fun_var(fun(Map) ->
			      TmpArgTypes = lookup_type_list(Args, Map),
			      erl_bif_types:type(erlang, '++', 2, TmpArgTypes)
			  end, Args),
  Cs = mk_constraints(Args, sub, ArgTypes),
  mk_conj_constraint_list([mk_constraint(Dst, sub, ReturnType),
			   mk_constraint(Hd, sub, HdVar),
			   mk_constraint(Tl, sub, TlVar)
			   |Cs]);
get_bif_constr({erlang, is_atom, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_atom(), State);
get_bif_constr({erlang, is_binary, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_binary(), State);
get_bif_constr({erlang, is_bitstring, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_bitstr(), State);
get_bif_constr({erlang, is_boolean, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_boolean(), State);
get_bif_constr({erlang, is_float, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_float(), State);
get_bif_constr({erlang, is_function, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_fun(), State);
get_bif_constr({erlang, is_function, 2}, Dst, [Fun, Arity], _State) ->
  ArgFun = fun(Map) ->
	       DstType = lookup_type(Dst, Map),
	       case t_is_atom(true, DstType) of
		 true ->
		   ArityType = lookup_type(Arity, Map),
		   case t_number_vals(ArityType) of
		     unknown -> t_fun();
		     Vals -> t_sup([t_fun(X, t_any()) || X <- Vals])
		   end;
		 false -> t_any()
	       end
	   end,
  ArgV = mk_fun_var(ArgFun, [Dst, Arity]),
  mk_conj_constraint_list([mk_constraint(Dst, sub, t_boolean()),
  			   mk_constraint(Fun, sub, ArgV),
			   mk_constraint(Arity, sub, t_integer())]);
get_bif_constr({erlang, is_integer, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_integer(), State);
get_bif_constr({erlang, is_list, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_maybe_improper_list(), State);
get_bif_constr({erlang, is_number, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_number(), State);
get_bif_constr({erlang, is_pid, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_pid(), State);
get_bif_constr({erlang, is_port, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_port(), State);
get_bif_constr({erlang, is_reference, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_reference(), State);
get_bif_constr({erlang, is_record, 2}, Dst, [Var, Tag] = Args, _State) ->
  ArgFun = fun(Map) ->
	       case t_is_atom(true, lookup_type(Dst, Map)) of
		 true -> t_tuple();
		 false -> t_any()
	       end
	   end,
  ArgV = mk_fun_var(ArgFun, [Dst]),
  DstFun = fun(Map) ->
	       TmpArgTypes = lookup_type_list(Args, Map),
	       erl_bif_types:type(erlang, is_record, 2, TmpArgTypes)
	   end,
  DstV = mk_fun_var(DstFun, Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Var, sub, ArgV),
			   mk_constraint(Tag, sub, t_atom())]);
get_bif_constr({erlang, is_record, 3}, Dst, [Var, Tag, Arity] = Args, State) ->
  %% TODO: Revise this to make it precise for Tag and Arity.
  ArgFun =
    fun(Map) ->
	case t_is_atom(true, lookup_type(Dst, Map)) of
	  true ->
	    ArityType = lookup_type(Arity, Map),
	    case t_is_integer(ArityType) of
	      true ->
		case t_number_vals(ArityType) of
		  [ArityVal] ->
		    TagType = lookup_type(Tag, Map),
		    case t_is_atom(TagType) of
		      true ->
			AnyElems = lists:duplicate(ArityVal-1, t_any()),
			GenRecord = t_tuple([TagType|AnyElems]),
			case t_atom_vals(TagType) of
			  [TagVal] ->
			    case state__lookup_record(State, TagVal,
						      ArityVal - 1) of
			      {ok, Type} ->
				AllOpaques = State#state.opaques,
				case t_opaque_match_record(Type, AllOpaques) of
				  [Opaque] -> Opaque;
				  _ -> Type
				end;
			      error -> GenRecord
			    end;
			  _ -> GenRecord
			end;
		      false -> t_tuple(ArityVal)
		    end;
		  _ -> t_tuple()
		end;
	      false -> t_tuple()
	    end;
	  false -> t_any()
	end
    end,
  ArgV = mk_fun_var(ArgFun, [Tag, Arity, Dst]),
  DstFun = fun(Map) ->
	       [TmpVar, TmpTag, TmpArity] = TmpArgTypes = lookup_type_list(Args, Map),
	       TmpArgTypes2 =
		 case lists:member(TmpVar, State#state.opaques) of
		   true ->
		     case t_is_integer(TmpArity) of
		       true ->
			 case t_number_vals(TmpArity) of
			   [TmpArityVal] ->
			     case t_is_atom(TmpTag) of
			       true ->
				 case t_atom_vals(TmpTag) of
				   [TmpTagVal] ->
				     case state__lookup_record(State, TmpTagVal, TmpArityVal - 1) of
				       {ok, TmpType} ->
					 case t_is_none(t_inf(TmpType, TmpVar, opaque)) of
					   true  -> TmpArgTypes;
					   false -> [TmpType, TmpTag, TmpArity]
					 end;
				       error -> TmpArgTypes
				     end;
				   _ -> TmpArgTypes
				 end;
			       false -> TmpArgTypes
			     end;
			   _ -> TmpArgTypes
			 end;
		       false -> TmpArgTypes
		     end;
		   false -> TmpArgTypes
		 end,
	       erl_bif_types:type(erlang, is_record, 3, TmpArgTypes2)
	   end,
  DstV = mk_fun_var(DstFun, Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
  			   mk_constraint(Var, sub, ArgV),
  			   mk_constraint(Tag, sub, t_atom()),
			   mk_constraint(Arity, sub, t_integer())]);
get_bif_constr({erlang, is_tuple, 1}, Dst, [Arg], State) ->
  get_bif_test_constr(Dst, Arg, t_tuple(), State);
get_bif_constr({erlang, 'and', 2}, Dst, [Arg1, Arg2] = Args, _State) ->
  True = t_from_term(true),
  False = t_from_term(false),
  ArgFun = fun(Var) ->
	       fun(Map) ->
		   DstType = lookup_type(Dst, Map),
		   case t_is_atom(true, DstType) of
		     true -> True;
		     false ->
		       case t_is_atom(false, DstType) of
			 true ->
			   case t_is_atom(true, lookup_type(Var, Map)) of
			     true -> False;
			     false -> t_boolean()
			   end;
			 false ->
			   t_boolean()
		       end
		   end
	       end
	   end,
  DstFun = fun(Map) ->
	       Arg1Type = lookup_type(Arg1, Map),
	       case t_is_atom(false, Arg1Type) of
		 true -> False;
		 false ->
		   Arg2Type = lookup_type(Arg2, Map),
		   case t_is_atom(false, Arg2Type) of
		     true -> False;
		     false ->
		       case (t_is_atom(true, Arg1Type)
			     andalso t_is_atom(true, Arg2Type)) of
			 true -> True;
			 false -> t_boolean()
		       end
		   end
	       end
	   end,
  ArgV1 = mk_fun_var(ArgFun(Arg2), [Arg2, Dst]),
  ArgV2 = mk_fun_var(ArgFun(Arg1), [Arg1, Dst]),
  DstV = mk_fun_var(DstFun, Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Arg1, sub, ArgV1),
			   mk_constraint(Arg2, sub, ArgV2)]);
get_bif_constr({erlang, 'or', 2}, Dst, [Arg1, Arg2] = Args, _State) ->
  True = t_from_term(true),
  False = t_from_term(false),
  ArgFun = fun(Var) ->
	       fun(Map) ->
		   DstType = lookup_type(Dst, Map),
		   case t_is_atom(false, DstType) of
		     true -> False;
		     false ->
		       case t_is_atom(true, DstType) of
			 true ->
			   case t_is_atom(false, lookup_type(Var, Map)) of
			     true -> True;
			     false -> t_boolean()
			   end;
			 false ->
			   t_boolean()
		       end
		   end
	       end
	   end,
  DstFun = fun(Map) ->
	       Arg1Type = lookup_type(Arg1, Map),
	       case t_is_atom(true, Arg1Type) of
		 true -> True;
		 false ->
		   Arg2Type = lookup_type(Arg2, Map),
		   case t_is_atom(true, Arg2Type) of
		     true -> True;
		     false ->
		       case (t_is_atom(false, Arg1Type)
			     andalso t_is_atom(false, Arg2Type)) of
			 true -> False;
			 false -> t_boolean()
		       end
		   end
	       end
	   end,
  ArgV1 = mk_fun_var(ArgFun(Arg2), [Arg2, Dst]),
  ArgV2 = mk_fun_var(ArgFun(Arg1), [Arg1, Dst]),
  DstV = mk_fun_var(DstFun, Args),
  F = fun(A) ->
	  try [mk_constraint(A, sub, True)]
	  catch throw:error -> []
	  end
      end,
  Constrs = F(Arg1) ++ F(Arg2),
  Disj = mk_disj_constraint_list([mk_constraint(Dst, sub, False)|Constrs]),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Arg1, sub, ArgV1),
			   mk_constraint(Arg2, sub, ArgV2),
			   Disj]);
get_bif_constr({erlang, 'not', 1}, Dst, [Arg] = Args, _State) ->
  True = t_from_term(true),
  False = t_from_term(false),
  Fun = fun(Var) ->
	    fun(Map) ->
		Type = lookup_type(Var, Map),
		case t_is_atom(true, Type) of
		  true -> False;
		  false ->
		    case t_is_atom(false, Type) of
		      true -> True;
		      false -> t_boolean()
		    end
		end
	    end
	end,
  ArgV = mk_fun_var(Fun(Dst), [Dst]),
  DstV = mk_fun_var(Fun(Arg), Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
         		   mk_constraint(Arg, sub, ArgV)]);
get_bif_constr({erlang, '=:=', 2}, Dst, [Arg1, Arg2] = Args, _State) ->
  ArgFun =
    fun(Self, OtherVar) ->
	fun(Map) ->
	    DstType = lookup_type(Dst, Map),
	    OtherVarType = lookup_type(OtherVar, Map),
	    case t_is_atom(true, DstType) of
	      true -> OtherVarType;
	      false ->
		case t_is_atom(false, DstType) of
		  true ->
		    case is_singleton_type(OtherVarType) of
		      true -> t_subtract(lookup_type(Self, Map), OtherVarType);
		      false -> t_any()
		    end;
		  false ->
		    t_any()
		end
	    end
	end
    end,
  DstFun = fun(Map) ->
	       ArgType1 = lookup_type(Arg1, Map),
	       ArgType2 = lookup_type(Arg2, Map),
	       case t_is_none(t_inf(ArgType1, ArgType2)) of
		 true -> t_from_term(false);
		 false -> t_boolean()
	       end
	   end,
  DstArgs = [Dst, Arg1, Arg2],
  ArgV1 = mk_fun_var(ArgFun(Arg1, Arg2), DstArgs),
  ArgV2 = mk_fun_var(ArgFun(Arg2, Arg1), DstArgs),
  DstV = mk_fun_var(DstFun, Args),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Arg1, sub, ArgV1),
			   mk_constraint(Arg2, sub, ArgV2)]);
get_bif_constr({erlang, '==', 2}, Dst, [Arg1, Arg2] = Args, _State) ->
  DstFun = fun(Map) ->
	       TmpArgTypes = lookup_type_list(Args, Map),
	       erl_bif_types:type(erlang, '==', 2, TmpArgTypes)
	   end,
  ArgFun =
    fun(Var, Self) ->
	fun(Map) ->
	    VarType = lookup_type(Var, Map),
	    DstType = lookup_type(Dst, Map),
	    case is_singleton_non_number_type(VarType) of
	      true ->
		case t_is_atom(true, DstType) of
		  true -> VarType;
		  false ->
		    case t_is_atom(false, DstType) of
		      true -> t_subtract(lookup_type(Self, Map), VarType);
		      false -> t_any()
		    end
		end;
	      false ->
		case t_is_atom(true, DstType) of
		  true ->
		    case t_is_number(VarType) of
		      true -> t_number();
		      false ->
			case t_is_atom(VarType) of
			  true -> VarType;
			  false -> t_any()
			end
		    end;
		  false ->
		    t_any()
		end
	    end
	end
    end,
  DstV = mk_fun_var(DstFun, Args),
  ArgL = [Arg1, Arg2, Dst],
  ArgV1 = mk_fun_var(ArgFun(Arg2, Arg1), ArgL),
  ArgV2 = mk_fun_var(ArgFun(Arg1, Arg2), ArgL),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Arg1, sub, ArgV1),
			   mk_constraint(Arg2, sub, ArgV2)]);
get_bif_constr({erlang, element, 2} = _BIF, Dst, Args,
               #state{cs = Constrs} = State) ->
  GenType = erl_bif_types:type(erlang, element, 2),
  case t_is_none(GenType) of
    true -> ?debug("Bif: ~w failed\n", [_BIF]), throw(error);
    false ->
      Fun = fun(Map) ->
		[I, T] = ATs = lookup_type_list(Args, Map),
		ATs2 = case lists:member(T, State#state.opaques) of
			 true -> [I, erl_types:t_opaque_structure(T)];
			 false -> ATs
		       end,
		erl_bif_types:type(erlang, element, 2, ATs2)
	    end,
      ReturnType = mk_fun_var(Fun, Args),
      ArgTypes = erl_bif_types:arg_types(erlang, element, 2),
      Cs = mk_constraints(Args, sub, ArgTypes),
      NewCs =
        case find_element(Args, Constrs) of
          'unknown' -> Cs;
          Elem -> [mk_constraint(Dst, eq, Elem)|Cs]
        end,
      mk_conj_constraint_list([mk_constraint(Dst, sub, ReturnType)|NewCs])
  end;
get_bif_constr({M, F, A} = _BIF, Dst, Args, State) ->
  GenType = erl_bif_types:type(M, F, A),
  Opaques =  State#state.opaques,
  case t_is_none(GenType) of
    true -> ?debug("Bif: ~w failed\n", [_BIF]), throw(error);
    false ->
      UnopaqueFun =
	fun(T) -> case lists:member(T, Opaques)  of
		    true -> erl_types:t_unopaque(T, [T]);
		    false -> T
		  end
	end,
      ReturnType = mk_fun_var(fun(Map) ->
				  TmpArgTypes0 = lookup_type_list(Args, Map),
				  TmpArgTypes = [UnopaqueFun(T) || T<- TmpArgTypes0],
				  erl_bif_types:type(M, F, A, TmpArgTypes)
			      end, Args),
      case erl_bif_types:is_known(M, F, A) of
	false ->
	  case t_is_any(GenType) of
	    true ->
	      none;
	    false ->
	      mk_constraint(Dst, sub, ReturnType)
	  end;
	true ->
	  ArgTypes = erl_bif_types:arg_types(M, F, A),
	  Cs = mk_constraints(Args, sub, ArgTypes),
	  mk_conj_constraint_list([mk_constraint(Dst, sub, ReturnType)|Cs])
      end
  end.

eval_inv_arith('+', _Pos, Dst, Arg) ->
  erl_bif_types:type(erlang, '-', 2, [Dst, Arg]);
eval_inv_arith('*', _Pos, Dst, Arg) ->
  case t_number_vals(Arg) of
    [0] -> t_integer();
    _ ->
      TmpRet = erl_bif_types:type(erlang, 'div', 2, [Dst, Arg]),
      Zero = t_from_term(0),
      %% If 0 is not part of the result, it cannot be part of the argument.
      case t_is_subtype(Zero, Dst) of
	false -> t_subtract(TmpRet, Zero);
	true -> TmpRet
      end
  end;
eval_inv_arith('-', 1, Dst, Arg) ->
  erl_bif_types:type(erlang, '-', 2, [Arg, Dst]);
eval_inv_arith('-', 2, Dst, Arg) ->
  erl_bif_types:type(erlang, '+', 2, [Arg, Dst]).

range_inc(neg_inf) -> neg_inf;
range_inc(pos_inf) -> pos_inf;
range_inc(Int) when is_integer(Int) -> Int + 1.

range_dec(neg_inf) -> neg_inf;
range_dec(pos_inf) -> pos_inf;
range_dec(Int) when is_integer(Int) -> Int - 1.

get_bif_test_constr(Dst, Arg, Type, State) ->
  ArgFun = fun(Map) ->
	       DstType = lookup_type(Dst, Map),
	       case t_is_atom(true, DstType) of
		 true -> Type;
		 false -> t_any()
	       end
	   end,
  ArgV = mk_fun_var(ArgFun, [Dst]),
  DstFun = fun(Map) ->
	       ArgType = lookup_type(Arg, Map),
	       case t_is_none(t_inf(ArgType, Type)) of
		 true ->
		   case lists:member(ArgType, State#state.opaques) of
		     true ->
		       OpaqueStruct = erl_types:t_opaque_structure(ArgType),
		       case t_is_none(t_inf(OpaqueStruct, Type)) of
			 true -> t_from_term(false);
			 false ->
			   case t_is_subtype(ArgType, Type) of
			     true -> t_from_term(true);
			     false -> t_boolean()
			   end
		       end;
		     false ->  t_from_term(false)
		   end;
		 false ->
		   case t_is_subtype(ArgType, Type) of
		     true -> t_from_term(true);
		     false -> t_boolean()
		   end
	       end
	   end,
  DstV = mk_fun_var(DstFun, [Arg]),
  mk_conj_constraint_list([mk_constraint(Dst, sub, DstV),
			   mk_constraint(Arg, sub, ArgV)]).
			   
			   
			   
%%=============================================================================
%%
%%  Errors inference.
%%
%%=============================================================================

infer_errors(Fun,Solution,State,TreeDict) ->
	Cs = state__get_cs_slicing(Fun, State),
	%ppDictSol(dict:to_list(Solution)),
	%io:format("Cs: ~p\n",[Cs]),
	%io:format("Res: ~p\n",[infer_case_covering(Cs,Solution,State,TreeDict)]),
	CaseErrors = 
		try 
		 infer_case_covering(Cs,TreeDict,Solution)
	        catch
	          _:_ -> []
	        end,
        ListErrors = 
		try 
		 infer_improper_list(Cs,Solution,State,TreeDict)
	        catch
	          _:_ -> []
	        end,
	%io:format("{CaseErrors,ListErrors}: ~w\n",[{CaseErrors,ListErrors}]),
	CaseErrors++ListErrors.

infer_improper_list(Cs,Solution,State,TreeDict)->
	infer_improper_list_1(Cs,dict:to_list(Solution),Solution,State,TreeDict).

infer_improper_list_1(Cs,[{Id,TypeLbls} | TypesLbls],Solution,State,TreeDict) ->
	[{Type,Lbls}|_] = lists:reverse(TypeLbls),
	LblsIL = 
	 case erl_types:t_is_cons(Type) of
	      true -> 
	      	%check whether some of the labels corresponds to a case expresion (TreeDict is used for that)
	      	Consts = look_for_associated_consts(Id,Cs),
	      	case look_for_list_tail(Consts) of
	      	     [] -> [];
	      	     [ListsTail|_] -> 
		      	ErrLbls = find_no_lists(ListsTail,Solution),
		      	case ErrLbls of 
		      	     [] -> [];
		      	     _ -> 
			      	clean_lbls(remove_duplicates(ErrLbls++Lbls),TreeDict)
			end
		 end;
	      false -> 
	      	[]
	 end,
	case LblsIL of
	     [] -> 
	     	infer_improper_list_1(Cs,TypesLbls,Solution,State,TreeDict);
	     _ -> 
		[{0,0,0,LblsIL,0,0}|infer_improper_list_1(Cs,TypesLbls,Solution,State,TreeDict)]
	end;
infer_improper_list_1(_,[],_,_,_) -> [].

clean_lbls(LblProducing,TreeDict) ->
	LblErrors = lists:sort(LblProducing),
	LabelsInside = calculate_inside_labels(TreeDict,LblErrors),
	discard_outermost_labels(LabelsInside).
	
look_for_associated_consts(Id,C) ->
	case C of
	     #constraint_list_slicing{} ->
	        lists:flatten([look_for_associated_consts(Id,C_) || C_ <- C#constraint_list_slicing.list]);
	     #constraint_slicing{} ->
	     	case C#constraint_slicing.cs#constraint.lhs of
	     	     {_,_,Id,_} -> [C];
	     	     _ -> 
	     	     	case C#constraint_slicing.cs#constraint.rhs of
	     	     	     {_,_,Id,_} -> [C];
	     	     	     _ -> []
	     	     	end
	     	end;
	     _ -> []
	end.	
	     	
look_for_list_tail([{constraint_slicing,{constraint,_,sub,{fun_var,_,Args},_},_}|Cs]) ->
        Tail = hd(Args),
	[Tail|look_for_list_tail(Cs)];
look_for_list_tail([_|Cs]) ->
	look_for_list_tail(Cs);
look_for_list_tail([]) ->
	[].
	
find_no_lists(T,Solution) -> 
	case dict:find(T,Solution) of
	     {ok,His} ->
	        {Current,_} = lists:last(His),
	        case erl_types:t_is_subtype(erl_types:t_cons(),Current) of
	             true -> [];
	             false -> 
	     		extract_first_no_list(His)
	     	end;
	     _ -> 
	     	[]
	end.
	
extract_first_no_list([{Type,Lbls}|Ts]) -> 
	case erl_types:t_is_subtype(erl_types:t_cons(),Type) of
	     true -> extract_first_no_list(Ts);
	     false -> Lbls
	end;
extract_first_no_list([]) -> [].

infer_case_covering(Cs,Tree,Solution) -> 
	%io:format("CASE VARS: ~p\n",[get_case_vars(Cs)]),
	CaseVars = get_case_vars(Cs),
	infer_case_covering_1(CaseVars,Solution,Tree).
	
infer_case_covering_1([{Vars,_}|VarLbls],Sol,Tree) ->
	%io:format("{Vars,Lbls}: ~w\n",[{Vars,Lbls}]),
	CaseVar = hd(Vars),
	Value = case dict:find(CaseVar,Sol) of
	                {ok,Value_} -> Value_;
	                _ -> no_value
		end,
	%io:format("Value: ~w\n",[Value]),
	%io:format("get(cases): ~p\n\n\nTOTAL: ~p\n",[get(cases),length(get(cases))]),
	InfoCase = [{LblArg,Clauses} || {LblArg,{c,var,CaseVar_,_},Clauses} <- get(cases),CaseVar_ =:= CaseVar],
	%io:format("info_case: ~p\n",[InfoCase]), 
	case InfoCase of
	       [] -> 
	       	  infer_case_covering_1(VarLbls,Sol,Tree);
	       [{LblArg,Clauses}|_] ->
	          RhsLbls = get_rhs_vars(Clauses),
	          %io:format("RhsLbls: ~p\n",[lists:sort(RhsLbls)]),
	          {ErrorLbls_,_} = search_problematic_clauses(Clauses,LblArg,Value,{erl_types:t_none(),[]},RhsLbls),
	          ErrorLbls__ = 
	            [{sets:to_list(sets:subtract(sets:from_list(ErrorLbl), sets:from_list(RhsLbls))),Always} ||
	              {ErrorLbl,Always} <- ErrorLbls_],       
	          %io:format("ErrorLbls__: ~w\n",[lists:sort(ErrorLbls__)]),
	          %io:format("ErrorLbls_: ~p\n",[ErrorLbls_]),
	          [{0,0,0,Cleaned++Always,0,0} || 
	             {LErrorLbls,Always} <- ErrorLbls__, 
	             (Cleaned = clean_lbls(remove_duplicates(LErrorLbls),Tree)) =/=[]]
	          ++ infer_case_covering_1(VarLbls,Sol,Tree)
	          
	end;
infer_case_covering_1([],_,_) -> [].


search_problematic_clauses([C|Cs],LblArg,Value,AccType,Removable0) -> 
	[Pat|_] = cerl:clause_pats(C),
	LblC = 
	      try
	        [cerl_trees_:get_label(C)]
	      catch
	      	{missing_label, _} -> []
	      end,
	TypePat = get_type_pat(Pat),
	%io:format("TypePats: ~w\n",[TypePat]),
	ProbPat = check_problematic_pattern(TypePat,Value,AccType),
	%io:format("ProbPat: ~w\n",[ProbPat]), 
	case ProbPat of
	     [] -> 
	       case TypePat of
	            {no_type,Lbls} -> 
	            	search_problematic_clauses(Cs,LblArg,Value,AccType,Removable0++Lbls);
	            {var,Lbls} -> 
	            	search_problematic_clauses(Cs,LblArg,Value,AccType,Removable0++Lbls);
	            {Type,Lbls} ->  
	            	{TypeAcc,LblAcc} = AccType,
	            	search_problematic_clauses(Cs,LblArg,Value,
	            	                           {erl_types:t_sup(TypeAcc,Type),
	            	                           Lbls++LblAcc},
	            	                           Removable0++Lbls)
	        end;
	      _ -> 
	      	case TypePat of
	      	     {var,Lbls} ->
	      	        {Prob,Removable} = search_problematic_clauses(Cs,LblArg,Value,AccType,Removable0++Lbls),
	      	        %CleanedProb = sets:to_list(sets:subtract(sets:from_list(ProbPat), sets:from_list(Removable))),
	      	        %{[{CleanedProb,LblC}|Prob],Removable};
	      	        {[{ProbPat,[LblArg|LblC]}|Prob],Removable};
	      	      _ -> 
	      	        {Prob,Removable} = search_problematic_clauses(Cs,LblArg,Value,AccType,Removable0),
	      	        %io:format("{ProbPat,Removable}: ~w\n",[{lists:sort(remove_duplicates(ProbPat)),lists:sort(remove_duplicates(Removable))}]),
	      	        CleanedProb = sets:to_list(sets:subtract(sets:from_list(ProbPat), sets:from_list(Removable))),
	      	        {[{CleanedProb,[LblArg]}|Prob],Removable}
	      	end
	end;
search_problematic_clauses([],_,_,_,Removable) -> {[],Removable}.

check_problematic_pattern(TypePat,Value,AccType) ->
	case TypePat of
	     {var,Lbls} ->
	     	LastValue = lists:last(Value),
	     	{ValueType,LblsValue} = LastValue,
	     	{TypeAcc,LblAcc} = AccType,
		SubType = erl_types:t_is_subtype(TypeAcc,ValueType),
		case SubType of
		     true -> Lbls++LblAcc++LblsValue;
		     false -> []
		end;
	      {no_type,_} -> [];
	      {TypeP,Lbls} ->
	      	LastValue = lists:last(Value),
	      	{ValueType,LblsValue} = LastValue,
	      	SubType = erl_types:t_is_subtype(TypeP,ValueType),
	      	case SubType of
	      	     true -> [];
	      	     false ->
	      	        %io:format("{LblsValue,Lbls}: ~w\n",[{lists:sort(remove_duplicates(LblsValue)),lists:sort(remove_duplicates(Lbls))}]), 
	      	        LblsValue++Lbls
	      	end
	end.
	
get_type_pat(P) ->
      Unfolded = cerl:unfold_literal(P),
      Lbl = 
	      try
	        [cerl_trees_:get_label(P)]
	      catch
	      	{missing_label, _} -> []
	      end,
      TypeP = 
	      case cerl:type(Unfolded) of
		 'literal' ->
			  {t_from_term(cerl:concrete(P)),Lbl};
		 'var' ->
		   	{var,Lbl};
		  _ ->
		   	{no_type,Lbl}
	      end,
       TypeP.
       
get_rhs_vars([C|Cs]) ->
	Body = cerl:clause_body(C),
	RhsVarsC = 
	  cerl_trees_:fold(
	    fun(Tree,Acc) -> 
	        try
	          [cerl_trees_:get_label(Tree)|Acc]
	        catch
	      	  {missing_label, _} -> []
	        end
	     end,[] , Body),
	RhsVarsC ++ get_rhs_vars(Cs);
get_rhs_vars([]) -> [].


get_case_vars(C) ->
	case C of
	     #constraint_list_slicing{} ->
	        case C#constraint_list_slicing.type of
	             'conj' -> 
	                lists:flatten([get_case_vars(C_) ||
	     		          C_ <- C#constraint_list_slicing.list]);
	             'disj' -> 
	                {Vars,Lbls} = look_for_case_vars_list(C#constraint_list_slicing.list),
	                NVars = remove_non_duplicated(lists:sort(Vars)),
			NLbls = remove_non_duplicated(lists:sort(Lbls)),
	             	NLists_ = [get_case_vars(C_) ||
	     		           C_ <- C#constraint_list_slicing.list],
	     		[{NVars,NLbls}|lists:flatten(NLists_)];
	             _ ->
	             	[]
	        end;
	     _ -> []
	end. 

look_for_case_vars_list([C|Cs]) ->
        %io:format("\nC: ~p\n",[C]),
        {VarsCs,LblsCs} = look_for_case_vars_list(Cs),
        {VarsC,LblsC} =
	case C of
	     #constraint_list_slicing{} ->
	        case C#constraint_list_slicing.type of
	             'conj' -> 
	                look_for_case_vars(C#constraint_list_slicing.list);
	             'disj' -> 
	             	{[],[]};
	             _ ->
	             	{[],[]}
	        end;
	     _ -> {[],[]}
	end,
	{VarsC++VarsCs,LblsC++LblsCs};
look_for_case_vars_list([]) -> {[],[]}.

look_for_case_vars([C|Cs]) ->
	{VarsCs,LblsCs} = look_for_case_vars(Cs),
	{VarsC,LblsC} =
	case C of 
	     #constraint_slicing{} ->
	     	case C#constraint_slicing.cs#constraint.lhs of
	     	     {c,var,Id1,_} -> 
	     	     	case C#constraint_slicing.cs#constraint.rhs of
	     	     	     {c,var,Id2,_} -> {[Id1,Id2],C#constraint_slicing.lbls};
	     	     	     _ -> {[Id1],C#constraint_slicing.lbls}
	     	     	end;
	     	     _ -> 
	     	     	case C#constraint_slicing.cs#constraint.rhs of
	     	     	     {c,var,Id2,_} -> {[Id2],C#constraint_slicing.lbls};
	     	     	     _ -> {[],[]}
	     	     	end
	     	end;
	     _ -> {[],[]}
	 end,
	 {remove_duplicates(VarsC ++ VarsCs), remove_duplicates(LblsC ++ LblsCs)};
look_for_case_vars([]) -> {[],[]}.

remove_non_duplicated([E1,E2|T]) ->
	case E1 =:= E2 of
	     true -> [E1 | remove_non_duplicated([E || E <- T, E =/= E1])];
	     false -> remove_non_duplicated([E2|T])
	end;
remove_non_duplicated(_) -> [].


%%=============================================================================
%%
%%  Constraint solver.
%%
%%=============================================================================

solve([Fun], State) ->
  ?debug("============ Analyzing Fun: ~w ===========\n",
	 [debug_lookup_name(Fun)]),
  %io:format("entraFun\n",[]),
  S=solve_fun(Fun, dict:new(), State),
  %io:format("\n\nsaleFun: ~p\n\n",[S]),
  S;
solve([_|_] = SCC, State) ->
  ?debug("============ Analyzing SCC: ~w ===========\n",
	 [[debug_lookup_name(F) || F <- SCC]]), 
  solve_scc(SCC, dict:new(), State, false).

solve_fun(Fun, FunMap, State) ->
  Cs = state__get_cs(Fun, State),
  Deps = get_deps(Cs),
  Ref = mk_constraint_ref(Fun, Deps),
  %% Note that functions are always considered to succeed.
  {ok, _MapDict, NewMap,MapSlicing,ErrorInfo} = solve_ref_or_list(Ref, FunMap, dict:new(), dict:new(), State),
  %io:format("ErrorInfo: ~p\n",[ErrorInfo]),
  NewType = lookup_type(Fun, NewMap),
  %io:format("Fun: ~p\nCs: ~p\n",[Fun,Cs]),
  TypeVar = lookup_type_var_cs(Fun,Cs),
%  io:format("Args: ~p\nRangue: ~p\n",
%  	    [erl_types:t_fun_args(TypeVar),erl_types:t_fun_range(TypeVar)]),
  case erl_types:t_is_fun(TypeVar) of
       true -> Lbl = look_for_args_lbl(erl_types:t_fun_args(TypeVar)++[erl_types:t_fun_range(TypeVar)],MapSlicing);
       false -> Lbl = []
  end,
  %io:format("\nSlicingMapping: \n",[]),
  %ppDictSol(dict:to_list(MapSlicing)),
  %io:format("Lbl: ~w\n",[Lbl]),
  %Pid = self(),
%  spawn(fun() -> Res = infer_errors(Fun,MapSlicing,State,TreeDict),Pid!{ended,Res} end),
%  InferredErrors = 
%	  receive 
%	  	{ended,Res} -> Res
%	  after
%	  	100 -> []
%	  end,
  InferredErrors = infer_errors(Fun,MapSlicing,State,get(tree)),
  NewFunMap1 =
   case state__get_rec_var(Fun, State) of
		 error -> FunMap;
		 {ok, Var} -> enter_type(Var, NewType, FunMap)
	       end,
  FinalMap = enter_type(Fun, NewType, NewFunMap1),
  {FinalMap,dict:from_list([{Fun,Lbl}]),ErrorInfo++InferredErrors}.
  
lookup_type_var_cs(Fun,{constraint_list,_,Cs,_,_})->
   lookup_type_var_cs_list(Fun,Cs).
  
lookup_type_var_cs_list(Fun,[{constraint,T,eq,Fun,_}|Cs]) ->
    case erl_types:t_is_fun(T) of
    	 true -> T;
    	 _ -> lookup_type_var_cs_list(Fun,Cs)
    end;
lookup_type_var_cs_list(Fun,[_|Cs]) -> lookup_type_var_cs_list(Fun,Cs);
lookup_type_var_cs_list(_,[]) -> erl_types:t_any().


look_for_args_lbl([Var|Vars],MapSlicing)->
   [case erl_types:t_is_var(Var) of
        true->
         case dict:find(erl_types:t_var_name(Var),MapSlicing) of
              {ok,Val} -> lists:sort(remove_duplicates(Val));
              _ -> []
         end;
        false -> []
   end |look_for_args_lbl(Vars,MapSlicing)];
look_for_args_lbl([],_) -> [].
      
remove_duplicates([{Type,L}|Tail]) -> [{Type,lists:sort(sets:to_list(sets:from_list(L)))} | remove_duplicates(Tail)];
remove_duplicates(L=[_|_]) -> lists:sort(sets:to_list(sets:from_list(L)));%[Other | remove_duplicates(Tail)];
remove_duplicates([]) -> [];
remove_duplicates(Other) -> Other.

solve_scc(SCC, Map, State, TryingUnit) ->
  State1 = state__mark_as_non_self_rec(SCC, State),
  Vars0 = [{Fun, state__get_rec_var(Fun, State)} || Fun <- SCC],
  Vars = [Var || {_, {ok, Var}} <- Vars0],
  Funs = [Fun || {Fun, {ok, _}} <- Vars0],
  Types = unsafe_lookup_type_list(Funs, Map),
  RecTypes = [t_limit(Type, ?TYPE_LIMIT) || Type <- Types],
  CleanMap = lists:foldl(fun(Fun, AccFunMap) ->
			     dict:erase(t_var_name(Fun), AccFunMap)
			 end, Map, SCC),
  Map1 = enter_type_lists(Vars, RecTypes, CleanMap),
  ?debug("Checking SCC: ~w\n", [[debug_lookup_name(F) || F <- SCC]]),
%  SolveFun = fun(X, Y) -> scc_fold_fun(X, Y, State1) end,
%  Map2 = lists:foldl(SolveFun, Map1, SCC),
  {Map2,Lbl,ErrorInfo} = scc_fold_fun_list(SCC,Map1,State1),
  FunSet = ordsets:from_list([t_var_name(F) || F <- SCC]),
  case maps_are_equal(Map2, Map, FunSet) of
    true ->
      ?debug("SCC ~w reached fixpoint\n", [SCC]),
      NewTypes = unsafe_lookup_type_list(Funs, Map2),
      case lists:all(fun(T) -> t_is_none(t_fun_range(T)) end, NewTypes)
	andalso TryingUnit =:= false of
	true ->
	  UnitTypes = [t_fun(state__fun_arity(F, State), t_unit())
		       || F <- Funs],
	  Map3 = enter_type_lists(Funs, UnitTypes, Map2),
	  solve_scc(SCC, Map3, State, true);
	false ->
	  {Map2,dict:from_list(Lbl),ErrorInfo}
      end;
    false ->
      ?debug("SCC ~w did not reach fixpoint\n", [SCC]),
      solve_scc(SCC, Map2, State, TryingUnit)
  end.
  
  
scc_fold_fun_list([F|Fs],Map,State = #state{var_lbl = VarLbl0})->
   {Map1,Lbl1,ErrorInfo1} = scc_fold_fun(F, Map, State),
   %io:format("\n\n\nF: ~p\nLbl:~w\n\n\n",[F,Lbl1]),
   State1 = 
     case Lbl1 of
          [] -> State;
          [_|_] -> 
            [LblFDst | LblFArgs_] = lists:reverse(Lbl1),
            LblFArgs = lists:reverse(LblFArgs_),
            %io:format("\n\n\nVL: ~w\nCP: ~w\n\n\n",[dict:to_list(VarLbl0),dict:to_list(change_pending(F,[LblFDst|LblFArgs],VarLbl0))]),
            State#state{var_lbl = change_pending(F,[LblFDst|LblFArgs],VarLbl0)}
     end,
   {Map2,Lbl2,ErrorInfo2} = scc_fold_fun_list(Fs, Map1, State1),
   case Lbl2 of
        no_lbl -> {Map2,[{F,Lbl1}],ErrorInfo1++ErrorInfo2};
        _ -> {Map2,[{F,Lbl1}|Lbl2],ErrorInfo1++ErrorInfo2}
   end;
scc_fold_fun_list([],Map,_) -> {Map,no_lbl,[]}.

scc_fold_fun(F, FunMap, State) ->
  Cs = state__get_cs(F, State),
  Deps = get_deps(Cs),
  Ref = mk_constraint_ref(F, Deps),
  %% Note that functions are always considered to succeed.
  {ok, _NewMapDict, Map,MapSlicing,_,ErrorInfo} = solve_ref_or_list(Ref, FunMap, dict:new(), dict:new(), State),
  NewType0 = unsafe_lookup_type(F, Map),
  NewType = t_limit(NewType0, ?TYPE_LIMIT),
  TypeVar = lookup_type_var_cs(F,Cs),
  Lbl = look_for_args_lbl(erl_types:t_fun_args(TypeVar)++[erl_types:t_fun_range(TypeVar)],MapSlicing),
  NewFunMap = case state__get_rec_var(F, State) of
		{ok, R} ->
		  enter_type(R, NewType, enter_type(F, NewType, FunMap));
		error ->
		  enter_type(F, NewType, FunMap)
	      end,
  %io:format("\nDone solving for function ~w\n", [F]),
  %io:format("\nMapping:~n"),
  %ppDictSol(dict:to_list(NewFunMap)),
  ?debug("Done solving for function ~w :: ~s\n", [debug_lookup_name(F),
						  format_type(NewType)]),
  {NewFunMap,Lbl,ErrorInfo}.
  
change_pending(F,Lbls,VarLbl)->
   dict:from_list(
     [{K,remove_duplicates(lists:flatten(change_pending_list(F,Lbls,VarLbl,L)))}
       ||{K,L}<-dict:to_list(VarLbl)]). 
   
change_pending_list({_,_,F,_},Lbls,VarLbl,[H|T])->
   NH=
    case H of
         {pending,F,Pos} -> lists:nth(Pos,Lbls);
         _ -> H
    end,
   [NH|change_pending_list(F,Lbls,VarLbl,T)];
change_pending_list(F,Lbls,VarLbl,[H|T])->
   [H|change_pending_list(F,Lbls,VarLbl,T)];
change_pending_list(_,_,_,[]) -> [].
         
 
  
ignore_pendings(Dict)->
   dict:from_list([ {K,lists:filter(fun ({pending,_,_})->false; (_) -> true end, L)} 
                    || {K,L}<-dict:to_list(Dict)]).

calculate_inside_labels(TreeDict,[Lbl|Lbls]) ->
%   io:format("Lbl:~p\nDict:~p\n",[Lbl,lists:sort(dict:fetch_keys(TreeDict))]),
%   try
%    io:format("Lbl:~p\nDict:~p\nFETCH:~p\n",[Lbl,lists:sort(dict:fetch_keys(TreeDict)),dict:fetch(Lbl,TreeDict)])
%   catch
%    _ -> io:format("PETA\n")
%   end,
    [
%     try
      {Lbl,cerl_trees_:get_lbls_from_tree(dict:fetch(Lbl,TreeDict))}
%     catch  
%      _ -> {Lbl,[]}
%     end
     | calculate_inside_labels(TreeDict,Lbls)];
calculate_inside_labels(_,[]) -> [].

discard_outermost_labels([{Lbl,InsideLbls}|Lbls]) ->
   DiscardedLbls = [LblTuple || LblTuple = {_,InsideLbls_} <- Lbls,Lbl_ <- InsideLbls_,Lbl_ == Lbl],
   FilteredLbls =  [LblTuple || LblTuple<-Lbls,lists:member(LblTuple,DiscardedLbls)==false],
   case [Lbl1||Lbl1<-InsideLbls,{Lbl2,_}<-Lbls,Lbl1==Lbl2] of
        [] -> [Lbl | discard_outermost_labels(FilteredLbls)];
        _ -> discard_outermost_labels(FilteredLbls)
   end;
discard_outermost_labels([]) -> [].
  
%-> DEBUG_INFO  
%print_core_from_labels(TreeDict,[Lbl|Lbls]) ->
%   %io:format("lbl: ~w\nDict: ~p\n",[Lbl,dict:fetch_keys(TreeDict)]),
%   io:format("\n**************\nCore for label ~w:\n~p\n**************\n",[Lbl,dict:fetch(Lbl,TreeDict)]),
%   %io:format("\Labels:~w\n",[cerl_trees_:get_lbls_from_tree(dict:fetch(Lbl,TreeDict))]),
%   print_core_from_labels(TreeDict,Lbls);
%print_core_from_labels(_,[]) -> ok. 
%<- DEBUG_INFO

solve_ref_or_list(#constraint_ref{id = Id, deps = Deps},
		  Map, MapDict, MapSlicing, State) ->
  {OldLocalMap, Check} =
    case dict:find(Id, MapDict) of
      error -> {dict:new(), false};
      {ok, M} -> {M, true}
    end,
  ?debug("Checking ref to fun: ~w\n", [debug_lookup_name(Id)]),
  CheckDeps = ordsets:del_element(t_var_name(Id), Deps),
  case Check andalso maps_are_equal(OldLocalMap, Map, CheckDeps) of
    true ->
      ?debug("Equal\n", []),
%      io:format("\n\n\nEQUAL\n\n\n"),
      {ok, MapDict, Map, MapSlicing,[]};
    false ->
      ?debug("Not equal. Solving\n", []),
%      io:format("\n\n\nNOT EQUAL\n\n\n"),
      Cs = state__get_cs(Id, State),
      Cs_slicing = state__get_cs_slicing(Id, State),
      Res =
	case state__is_self_rec(Id, State) of
	  true -> solve_self_recursive(Cs, Map, MapDict,MapSlicing, Id, t_none(), State);
	  false -> solve_ref_or_list(Cs, Map, MapDict, MapSlicing, State)
	end,
      %SLICING
      Res_ =
	case state__is_self_rec(Id, State) of
	  true -> solve_self_recursive(Cs, Map, MapDict, MapSlicing, Id, t_none(), State);
	  false -> solve_ref_or_list(Cs_slicing, Map, MapDict, MapSlicing, State)
	end,
%-> DEBUG_INFO  
%       case Res of
%	     {error,_} ->
%		  io:format("\n*********************SOLVE*******************\n",[]),
%%       		  io:format("\nMapping:~n",[]),
%%       		  ppDictSol(dict:to_list(DictError)),
%       		  %io:format("Res_: ~p\n",[Res_]),
%	          case Res_ of
%		           {error,{_,{L,O,R,DictPrev,DictSlicing_,LblError,LblPrevious}}} ->
%%		              io:format("\nMapping slicing: \n",[]),
%%		              ppDictSol(dict:to_list(DictErrorSlicing)),
%		              io:format("\nConstraint failing:\n ~p\n \t~p\n ~p\n LABELS: ~w\n LABELS PREVIOUS: ~w\n",
%		                        [L,O,R,lists:sort(remove_duplicates(LblError)),lists:sort(remove_duplicates(LblPrevious))]),
%		               io:format("\nMapping before fail:~n",[]),
%		               ppDictSol(dict:to_list(DictPrev)),
%		               io:format("\nSlicingMapping: \n",[]),
%		               ppDictSol(dict:to_list(DictSlicing_)),
%		              Intersection = sets:intersection(sets:from_list(LblError),sets:from_list(LblPrevious)),
%		              Union = sets:union(sets:from_list(LblError),sets:from_list(LblPrevious)),
%		              LblProducing=sets:to_list(sets:subtract(Union,Intersection)),%sets:to_list(Union),
%		              %io:format("LblProducing: ~w\n",[{LblError,LblPrevious,Union,Intersection,LblProducing}]),
%		              LblError_ = lists:sort(LblProducing),
%		              io:format("\nLabels producing the error: ~w\n",[LblError_]),
%		              TreeDict = get(tree),
%		              LabelsInside = calculate_inside_labels(TreeDict,LblError_),
%		              LblErrorFiltered = discard_outermost_labels(LabelsInside),
%		              %ppDictSol(dict:to_list(get(tree))),
%		              print_core_from_labels(TreeDict,LblErrorFiltered);
%		           _ -> {ok, _, Map_Res_,MapSlicing_Res_}=Res_,
%		           	io:format("\nMapping:~n",[]),
%		                ppDictSol(dict:to_list(Map_Res_)),
%		                io:format("\nSlicingMapping: \n",[]),
%		                ppDictSol(dict:to_list(MapSlicing_Res_))
%		                %io:format("\nNot slicing error.\nMapping slicing : ~w~n",[Res_])
%	           end,
%	      io:format("\n*********************************************\n",[]);
%	    _ -> ok
%	 end,
%	 case {Res_,Res} of
%	     {{error,_},{ok,_}} ->
%		  io:format("\n*********************SOLVE ONLY SLICING ERROR*******************\n",[]),
%       		  io:format("\nMapping: ~w~n",[Res]),
%	          io:format("\nMapping slicing: ~w~n",[Res_]),
%	          case Res_ of
%		           {error,{_,{_,_,_,_,_,LblError___,LblPrevious_}}} ->
%		              LblError__ = lists:sort(sets:to_list(sets:from_list(lists:flatten(LblError___++LblPrevious_)))),
%		              io:format("\nLabels producing the error: ~w\n",[LblError__]),
%		              print_core_from_labels(get(tree),LblError__);
%		           _ -> ok
%	           end,
%	      io:format("\n*********************************************\n",[]);
%	    _ -> ok
%	 end,
%<- DEBUG_INFO
      case Res of
		{error, NewMapDict} ->
		  ?debug("Error solving for function ~p\n", [debug_lookup_name(Id)]),
		  Arity = state__fun_arity(Id, State),
		  FunType =
		    case state__prop_domain(t_var_name(Id), State) of
		      error -> t_fun(Arity, t_none());
		      {ok, Dom} -> t_fun(Dom, t_none())
		    end,
		  NewMap1 = enter_type(Id, FunType, Map),
		  NewMap2 =
		    case state__get_rec_var(Id, State) of
		      {ok, Var} -> enter_type(Var, FunType, NewMap1);
		      error -> NewMap1
		    end,
		  ErrorInfo =
		    case Res_ of
		         {error,{_,{L_,O_,R_,DictPrev_,DictSlicing__,LblErrors,LblPrevious__}}} ->
		              Intersection_ = sets:intersection(sets:from_list(LblErrors),sets:from_list(LblPrevious__)),
		              Union_ = sets:union(sets:from_list(LblErrors),sets:from_list(LblPrevious__)),
		              LblProducing_ = sets:to_list(sets:subtract(Union_,Intersection_)),%sets:to_list(Union_),
		              LblErrors_ = lists:sort(LblProducing_),
		              LabelsInside_ = calculate_inside_labels(get(tree),LblErrors_),
		              LblErrorFiltered_ = discard_outermost_labels(LabelsInside_),
		              [{L_,O_,R_,LblErrorFiltered_,DictPrev_,DictSlicing__}];
		         _ -> []
		    end,
		  {ok, dict:store(Id, NewMap2, NewMapDict), NewMap2, MapSlicing,ErrorInfo};
		{ok, NewMapDict, NewMap,_,_} ->
		  {ok,_,_,NewMapSlicing,_}=Res_,
		  ?debug("Done solving fun: ~p\n", [debug_lookup_name(Id)]),
		  FunType = lookup_type(Id, NewMap),
		  NewMap1 = enter_type(Id, FunType, Map),
		  NewMap2 =
		    case state__get_rec_var(Id, State) of
		      {ok, Var} -> enter_type(Var, FunType, NewMap1);
		      error -> NewMap1
		    end,
		  {ok, dict:store(Id, NewMap2, NewMapDict), NewMap2, NewMapSlicing,[]}
      end
  end;
solve_ref_or_list(#constraint_list{type=Type, list = Cs, deps = Deps, id = Id} ,Map, MapDict, MapSlicing, State) ->
  %solve_ref_or_list_1(Type,lists:reverse(Cs),Deps,Id,Map, MapDict, MapSlicing, State);
  solve_ref_or_list_1(Type,Cs,Deps,Id,Map, MapDict, MapSlicing, State);
  
solve_ref_or_list(#constraint_list_slicing{type=Type, list = Cs, deps = Deps, id = Id} ,Map, MapDict, MapSlicing, State) ->
  %solve_ref_or_list_1(Type,lists:reverse(Cs),Deps,Id,Map, MapDict, MapSlicing, State).
  %io:format("ENTRA\n"),
  %ppDictSol(dict:to_list(MapSlicing)),
  solve_ref_or_list_1(Type,Cs,Deps,Id,Map, MapDict, MapSlicing, State).
  
solve_ref_or_list_1(Type,Cs,Deps,Id,Map, MapDict_, MapSlicing, State)->
%  io:format("\nCs: ~w\n",[Cs]),
  MapDict =
     case MapDict_ of
          {MapDict__,_} -> MapDict__;
          _ -> MapDict_
     end,
  {OldLocalMap, Check}=
     case dict:find(Id, MapDict) of
         error -> {dict:new(), false};
         {ok, M} -> {M, true}
     end,
%  io:format("\nId: ~w\n",[Id]),
%  io:format("\nCheck: ~p\n",[{Check, dict:to_list(OldLocalMap)}]),
  ?debug("Checking ref to list: ~w\n", [Id]),
  case Check andalso maps_are_equal(OldLocalMap, Map, Deps) andalso Id/=undefined of
    true ->
      ?debug("~w equal ~w\n", [Type, Id]),
      %io:format("\n\n\nEQUAL 2\n\n\n"),
      {ok, MapDict, Map,MapSlicing,[]};
    false ->
      ?debug("~w not equal: ~w. Solving\n", [Type, Id]),
      %io:format("\n\n\nNOT EQUAL 2\n\n\n"),
      %io:format("llama a solve_clist\n",[]),
      S=solve_clist(Cs, Type, Id, Deps, MapDict, Map, MapSlicing, State),
      case S of
          {ok, NewMapDict, NewMap, NewMapSlicing} -> 
            {ok, NewMapDict, NewMap, NewMapSlicing,[]};
          _ -> S
      end
      %io:format("FI solve_clist ~p\n",[S]),
      %S
  end.


solve_self_recursive(Cs, Map, MapDict, MapSlicing, Id, RecType0, State) ->
  ?debug("Solving self recursive ~w\n", [debug_lookup_name(Id)]),
  {ok, RecVar} = state__get_rec_var(Id, State),
  ?debug("OldRecType ~s\n", [format_type(RecType0)]),
  RecType = t_limit(RecType0, ?TYPE_LIMIT),
  Map1 = enter_type(RecVar, RecType, dict:erase(t_var_name(Id), Map)),
  ?debug("\tMap in: ~p\n",[[{X, format_type(Y)}||{X, Y}<-dict:to_list(Map1)]]),
  case solve_ref_or_list(Cs, Map1, MapDict, MapSlicing, State) of
    {error, _} = Error ->
      case t_is_none(RecType0) of
		true ->
		  %% Try again and assume that this is a non-terminating function.
		  Arity = state__fun_arity(Id, State),
		  NewRecType = t_fun(lists:duplicate(Arity, t_any()), t_unit()),
		  solve_self_recursive(Cs, Map, MapDict, MapSlicing, Id, NewRecType, State);
		false ->
		  Error
      end;
    {ok, NewMapDict, NewMap,NewMapSlicing,_} ->
      ?debug("\tMap: ~p\n",
	     [[{X, format_type(Y)} || {X, Y} <- dict:to_list(NewMap)]]),
      NewRecType = unsafe_lookup_type(Id, NewMap),
      case t_is_equal(NewRecType, RecType0) of
		true ->
		  {ok, NewMapDict, enter_type(RecVar, NewRecType, NewMap),NewMapSlicing};
		false ->
		  solve_self_recursive(Cs, Map, MapDict, MapSlicing, Id, NewRecType, State)
      end
  end.
  
  
%ppDictSol([{Id,Type}|Sol])->
%   %io:format("Type:~w\n",[Type]),
%   %Printed = (catch io:format("\tID: ~w TYPE: ~w\n",[Id,remove_duplicates(ppDictSol(dict:to_list(Type)))])),
%   %case Printed of
%   %     ok -> ok;
%   	%_ -> 
%          io:format("\tID: ~w TYPE: ~w\n",[Id,remove_duplicates(Type)]),
%   %end,
%   ppDictSol(Sol);
%ppDictSol([])->ok.

solve_clist(Cs, conj, Id, Deps, MapDict, Map, MapSlicing, State) ->
  case solve_cs(Cs, Map, MapDict, MapSlicing, State) of
    {error, _} = Error -> Error;
    {ok, NewMapDict, NewMap, NewMapSlicing} = Ret ->
      case Cs of
		[_] ->
		  %% Just a special case for one conjunctive constraint.
		  Ret;
		_ ->
		  case maps_are_equal(Map, NewMap, Deps) of
		    true -> %io:format("\n\n\nEQUAL 3\n\n\n"),
		            {ok, dict:store(Id, NewMap, NewMapDict), NewMap, NewMapSlicing};
		    false -> %io:format("\n\n\nNOT EQUAL 3 -> TORNA\n\n\n"),
		             solve_clist(Cs, conj, Id, Deps, NewMapDict, NewMap, NewMapSlicing, State) 
		  end
      end
  end;
solve_clist(Cs, disj, Id, _Deps, MapDict, Map,  MapSlicing, State) ->
%  io:format("\n\n\nENTRA ~w\n\n\n",[Cs]),
  Fun = fun(C, Dict) ->
	    case solve_ref_or_list(C, Map, Dict,  MapSlicing, State) of
	      {ok, NewDict, NewMap,NewMapSlicing,_} -> {{ok, NewMap,NewMapSlicing}, NewDict};
	      {error, _NewDict} = Error -> Error
	    end
	end,
  {Maps, NewMapDict} = lists:mapfoldl(Fun, MapDict, Cs),
%  io:format("\n\n\nSURT\n\n\n"),
  case lists:unzip([{X,Y} || {ok, X,Y} <- Maps]) of
    {[],[]} -> {error, NewMapDict};
    {MapList,MapSlicingList} ->
      NewMap = join_maps(MapList),
%      io:format("Maps: \n"),
%      [ppDictSol(dict:to_list(MapS))||MapS<-MapSlicingList],
%      ppDictSol(dict:to_list(MapSlicingList)),
%      io:format("\n\n\n\nNOU\n\n\n\n"),
      NewMapSlicing = join_maps_slicing(MapSlicingList),
%      io:format("NewMapSlicing: \n"),
%      ppDictSol(dict:to_list(NewMapSlicing)),
      NewMapDict_=
      case NewMapDict of
           {NewMapDict__,_} -> NewMapDict__;
           _ -> NewMapDict
      end,
      {ok, dict:store(Id, NewMap, NewMapDict_), NewMap, NewMapSlicing }
  end.

solve_cs([#constraint_ref{} = C|Tail], Map, MapDict, MapSlicing, State) ->
  case solve_ref_or_list(C, Map, MapDict, MapSlicing, State) of
    {ok, NewMapDict, Map1, MapSlicing1,_} -> solve_cs(Tail, Map1, NewMapDict, MapSlicing1, State);
    {error, _NewMapDict} = Error -> Error
  end;
solve_cs([#constraint_list{} = C|Tail], Map, MapDict, MapSlicing, State) ->
  case solve_ref_or_list(C, Map, MapDict, MapSlicing, State) of
    {ok, NewMapDict, Map1, MapSlicing1,_} -> solve_cs(Tail, Map1, NewMapDict, MapSlicing1,  State);
    {error, _NewMapDict} = Error -> Error
  end;
solve_cs([#constraint_list_slicing{} = C|Tail], Map, MapDict, MapSlicing, State) ->
  case solve_ref_or_list(C, Map, MapDict, MapSlicing, State) of
    {ok, NewMapDict, Map1, MapSlicing1,_} -> solve_cs(Tail, Map1, NewMapDict, MapSlicing1, State);
    {error, _NewMapDict} = Error -> Error
  end;
solve_cs([#constraint{} = C|Tail], Map, MapDict, MapSlicing, State) ->
  case solve_one_c(C, Map, State#state.opaques) of
    error ->
      ?debug("+++++++++++\nFailed: ~s :: ~s ~w ~s :: ~s\n+++++++++++\n",
	     [format_type(C#constraint.lhs),
	      format_type(lookup_type(C#constraint.lhs, Map)),
	      C#constraint.op,
	      format_type(C#constraint.rhs),
	      format_type(lookup_type(C#constraint.rhs, Map))]),
      {error, MapDict};
    {ok, NewMap} ->
      solve_cs(Tail, NewMap, MapDict, MapSlicing, State)
  end;
solve_cs([#constraint_slicing{cs = C, lbls = Lbl}|Tail], Map, MapDict, MapSlicing,#state{var_lbl = VarLbl0} = State) ->
  VarLbl = ignore_pendings(VarLbl0),
  case solve_one_c(C, Map, MapSlicing, State#state.opaques,Lbl,VarLbl) of
    {error,LblError} ->
      {error, {MapDict, LblError}};
    {ok, NewMap, NewMapSlicing} ->
%      io:format("NewMapSlicing:\n"),
%      ppDictSol(dict:to_list(NewMapSlicing)),
      solve_cs(Tail, NewMap, MapDict, NewMapSlicing, State)
  end;
solve_cs([], Map, MapDict, MapSlicing, _State) ->
  {ok, MapDict, Map, MapSlicing}.

solve_one_c(#constraint{lhs = Lhs, rhs = Rhs, op = Op}, Map, Opaques) ->
%  io:format("\n\nRestriccion anterior: ~p~n",[{Lhs,Op,Rhs}]),
  LhsType = lookup_type(Lhs, Map),
  RhsType = lookup_type(Rhs, Map),
%  io:format("\n\nTypes: ~p~n",[{LhsType,RhsType}]),
%  io:format("Map: \n"),
%  ppDictSol(dict:to_list(Map)),
  Inf = t_inf(LhsType, RhsType, opaque),
  ?debug("Solving: ~s :: ~s ~w ~s :: ~s\n\tInf: ~s\n",
	 [format_type(Lhs), format_type(LhsType), Op,
	  format_type(Rhs), format_type(RhsType), format_type(Inf)]),
  case t_is_none(Inf) of
    true -> error;
    false ->
      case Op of
	sub -> solve_subtype(Lhs, Inf, Map, Opaques);
	eq ->
	  case solve_subtype(Lhs, Inf, Map, Opaques) of
	    error -> error;
	    {ok, Map1} -> solve_subtype(Rhs, Inf, Map1, Opaques)
	  end
      end
  end.

solve_subtype(Type, Inf, Map, Opaques) ->
  %% case cerl:is_literal(Type) of
  %%   true ->
  %%     case t_is_subtype(t_from_term(cerl:concrete(Type)), Inf) of
  %%	true -> {ok, Map};
  %%	false -> error
  %%     end;
  %%   false ->
      try t_unify(Type, Inf, Opaques) of
		{_, List} -> {ok, enter_type_list(List, Map)}
      catch
		throw:{mismatch, _T1, _T2} ->
		  ?debug("Mismatch between ~s and ~s\n",
			 [format_type(_T1), format_type(_T2)]),
		  error
      end.
  %% end.
  
  
solve_one_c(#constraint{lhs = Lhs, rhs = Rhs, op = Op}, Map, 
            MapSlicing, Opaques, Lbl, VarLbl) ->
  %io:format("\n\nRestriccion: ~p~n",[{Lhs,Op,Rhs,erl_types:t_is_var(Lhs),erl_types:t_is_var(Rhs)}]),
  LhsType = lookup_type(Lhs, Map),
  RhsType = lookup_type(Rhs, Map),
  %io:format("\n\nTypes: ~p~n",[{LhsType,RhsType}]),
%  io:format("Map: \n"),
%  ppDictSol(dict:to_list(Map)),
%  io:format("MapSlicing: \n"),
%  ppDictSol(dict:to_list(MapSlicing)),
  Inf = t_inf(LhsType, RhsType, opaque),
  ?debug("Solving: ~s :: ~s ~w ~s :: ~s\n\tInf: ~s\n",
	 [format_type(Lhs), format_type(LhsType), Op,
	  format_type(Rhs), format_type(RhsType), format_type(Inf)]),
  Lhs_= 
   case Lhs of
    	{_,_,Lhs__,_} -> Lhs__;
    	_ -> Lhs
    end,
  Rhs_=
    case Rhs of
    	{_,_,Rhs__,_} -> Rhs__;
    	_ -> Rhs
    end,
  case t_is_none(Inf) of
    true -> LblPrevious = %lookup_type_slicing_lbl(Lhs_, MapSlicing,LhsType)
                          %++lookup_type_slicing_lbl(Rhs_, MapSlicing,RhsType),
            case erl_types:t_is_var(Lhs) and erl_types:t_is_var(Rhs) of
		  	    true -> look_for_conficts(Lhs_,Rhs_,MapSlicing);
		  	    false -> case erl_types:t_is_var(Lhs)  of
		  	                  true -> look_for_confict_with_type(RhsType,Lhs_,MapSlicing);
		  	                  false -> case erl_types:t_is_var(Rhs)  of
		  	                                true -> look_for_confict_with_type(LhsType,Rhs_,MapSlicing);
		  	                                false -> []
		  	                            end
		  	              end
	    end,
            %io:format("LblPrevious: ~p\n",[LblPrevious]),
            {error,{Lhs, Op, Rhs, Map,MapSlicing,Lbl,LblPrevious}};
    false ->
      case Op of
		sub -> 
		   % solve_subtype(Lhs, Inf, Map, MapSlicing, Opaques,Lbl,[], VarLbl);
		     case erl_types:t_is_equal(LhsType,Inf) of
		          true -> {ok,Map,MapSlicing};
		          _ -> solve_subtype(Lhs, Inf, Map, MapSlicing, Opaques,Lbl,[], VarLbl)
		     end;
		eq ->
		 LblRhs = 
		  	case erl_types:t_is_var(Lhs) and erl_types:t_is_var(Rhs) of
		  	    true -> lookup_type_slicing(Rhs_,MapSlicing);
		  	    false -> []
		  	end,
		  case solve_subtype(Lhs, Inf, Map, MapSlicing, Opaques,Lbl,LblRhs, VarLbl) of
		    {error,LblError} -> {error,LblError};
		    {ok, Map1,MapSlicing1} -> 
		         LblLhs = 
			  	case erl_types:t_is_var(Lhs) and erl_types:t_is_var(Rhs) of
			  	    true -> lookup_type_slicing(Lhs_,MapSlicing1);
			  	    false -> []
			  	end,
			 case erl_types:t_is_equal(RhsType,Inf) of
		              true -> {ok,Map1,MapSlicing1};
		              _ -> solve_subtype(Rhs, Inf, Map1, MapSlicing1, Opaques,Lbl,LblLhs, VarLbl)
		         end
		       %solve_subtype(Rhs, Inf, Map1, MapSlicing1, Opaques,Lbl,LblLhs, VarLbl)
		  end
      end
  end.

solve_subtype(Type, Inf, Map, MapSlicing, Opaques,Lbl,LblOther, VarLbl) ->
      %io:format("\nType:~p\nInf:~p\n",[Type,Inf]),
      try t_unify(Type, Inf, Opaques) of
		{_, List} -> 
%		  io:format("List: ~w\nLbl: ~w\nLblOther: ~w\nMapSlicing:\n",[List,Lbl,LblOther]),
%		  ppDictSol(dict:to_list(MapSlicing)),
%		  io:format("enter1:\n"),
%		  ppDictSol(dict:to_list(enter_type_slicing_list(List, Lbl, MapSlicing))),
%		  io:format("List: ~w\n",[Type]),
%		  io:format("VarLbl:\n"),
%		  ppDictSol(dict:to_list(VarLbl)),
		  %io:format("List: ~w\n",[{Type, Inf,List,dict:to_list(VarLbl)}]),
		  ExternalLbl = get_external_labels(List,VarLbl),
%		  case dict:find(Type,VarLbl) of
%		       {ok,Lbl_} -> Lbl_;
%		       error -> []
%		  end,
%		  io:format("ExternalLbl: ~w\n",[ExternalLbl]),
		  {ok, enter_type_list(List, Map),
		   enter_type_slicing_list_3(List,ExternalLbl,
		        enter_type_slicing_list_2(List,LblOther,
		            enter_type_slicing_list(List, Lbl, MapSlicing)))}
      catch
		throw:{mismatch, _T1, _T2} ->
		  ?debug("Mismatch between ~s and ~s\n",
			 [format_type(_T1), format_type(_T2)]),
		  {error,{Type, Inf, Map,MapSlicing,Lbl,[]}}
      end.
      
      
%lookup_type_slicing_lbl(Key, Map, Type) ->
%  case dict:find(Key, Map) of
%    error -> [];
%    {ok, List} -> %io:format("entra ~p\n",[{List, [Lbl_||P={Type_,Lbl_} <- List,io:format("~p\n",[P]) =:= ok]}]),
%                  lists:flatten([Lbl_||{Type_,Lbl_} <- List,Type =:= Type_])
%  end.

get_external_labels([{V,TypeV}|T],VarLbl)->
  [case dict:find(t_var(V),VarLbl) of
        {ok,Lbl_} -> [Lbl__ || Lbl__ = {TypeV_,_} <- Lbl_, TypeV /= any,not t_is_none(erl_types:t_inf(TypeV,TypeV_,opaque)) ];
        error -> []
   end | get_external_labels(T,VarLbl)];
get_external_labels([],_) -> [].
      
look_for_conficts(V1,V2,SDict) ->
    TypeLbl = 
    case dict:find(V1,SDict) of
         {ok,TL} -> TL;
         error -> []
    end,
    lists:flatten(
	[case look_for_confict_with_type(Type,V2,SDict) of
	      [] -> [];
	      LblC -> LblC++Lbl
	  end || {Type,Lbl} <- TypeLbl]).
	
look_for_confict_with_type(Type,V,SDict) ->
    TypeLbl = 
    case dict:find(V,SDict) of
         {ok,TL} -> TL;
         error -> []
    end,
   lists:flatten(
	[begin %io:format("TypesCompared: ~w\n",[{Type,TypeV,erl_types:t_inf(Type,TypeV,opaque)}]), 
	      case t_is_none(erl_types:t_inf(Type,TypeV,opaque)) of
	      true -> Lbl;
	      false -> []
	 end end || {TypeV,Lbl} <- TypeLbl]).
      
enter_type_slicing(Key, {Type,Lbl}, Map) when is_integer(Key) ->
  ?debug("Entering ~s :: ~s\n", [format_type(t_var(Key)), format_type(Type)]),
  case t_is_any(Type) of
    true ->
      dict:erase(Key, Map);
    false ->
      %io:format("\nentra\n"),
      LimitedVal = t_limit(Type, ?INTERNAL_TYPE_LIMIT),
      case dict:find(Key, Map) of
		{ok, LimitedVal} -> Map;
		{ok, Previous} -> case [Lbl_||{LimitedVal_,Lbl_}<-Previous,LimitedVal_==LimitedVal] of
		                       [] -> dict:append(Key, {LimitedVal,Lbl}, Map);
		                       _ ->
		                         %Map1 = dict:erase(KeyName,Map),
		                         F = fun ({Type_,Lbl1},Type_,Lbl2) -> {Type_,Lbl1 ++ Lbl2} ;
		                          	 ({Type_,Lbl1},_,_) -> {Type_,Lbl1}
		                             end,
		                         NAllTypeLbl = lists:map(fun (TL)-> F(TL,Type,Lbl) end,Previous),
		                         %io:format("\nentra\n"),
		                         %NAllTypeLbl = [{Type_,Lbl_ ++ Lbl}||{Type_,Lbl_}<-Previous,Type_==LimitedVal] ++
		                         %              [TL||TL={Type_,_}<-Previous,Type_ =/=LimitedVal],
		                         dict:store(Key, NAllTypeLbl, Map)              
		                  end;
		error -> dict:append(Key, {LimitedVal,Lbl}, Map)
      end
  end;
enter_type_slicing(Key, {Type,Lbl}, Map) ->
  ?debug("Entering ~s :: ~s\n", [format_type(Key), format_type(Type)]),
  enter_type_slicing(t_var_name(Key), {Type,Lbl}, Map).

%enter_type_lists([Key|KeyTail], [Val|ValTail], Map) ->
%  Map1 = enter_type(Key, Val, Map),
%  enter_type_lists(KeyTail, ValTail, Map1);
%enter_type_lists([], [], Map) ->
%  Map.      
      
enter_type_slicing_list([{Key, Val}|Tail], Lbl, Map) ->
  Map1 = enter_type_slicing(Key, {Val,Lbl}, Map),
  enter_type_slicing_list(Tail, Lbl, Map1);      
enter_type_slicing_list([],_,Map) -> Map.

enter_type_slicing_list_2([{Key, _}|Tail], TypeLbl, Map) ->
  Map1 = enter_type_slicing_2(Key, TypeLbl, Map),
  enter_type_slicing_list_2(Tail,TypeLbl, Map1);      
enter_type_slicing_list_2([],_,Map) -> Map.

enter_type_slicing_2(Key, [TypeLbl|Tail], Map)->
   enter_type_slicing(Key, TypeLbl, enter_type_slicing_2(Key, Tail, Map));
enter_type_slicing_2(_, [], Map) -> Map.

enter_type_slicing_list_3([{Key, _}|Tail], [TypeLbl|TailTypeLbl], Map) ->
  Map1 = enter_type_slicing_3(Key, TypeLbl, Map),
  enter_type_slicing_list_3(Tail,TailTypeLbl, Map1);      
enter_type_slicing_list_3([],_,Map) -> Map.

enter_type_slicing_3(Key, [TypeLbl|Tail], Map)->
   enter_type_slicing(Key, TypeLbl, enter_type_slicing_3(Key, Tail, Map));
enter_type_slicing_3(_, [], Map) -> Map.


join_maps_slicing(Maps) ->
  Keys = lists:foldl(fun(TmpMap, AccKeys) ->
			 [Key || Key <- AccKeys, dict:is_key(Key, TmpMap)]
		     end,
		     dict:fetch_keys(hd(Maps)), tl(Maps)),
  join_maps_slicing(Keys, Maps, dict:new()).

join_maps_slicing([Key|Left], Maps = [Map|MapsLeft], AccMap) ->
  %io:format("Key: ~p\n MapsLeft: ~p\n lookup_type_slicing(Key, Map): ~p\n",[Key,[dict:to_list(MapLeft)||MapLeft<-MapsLeft],lookup_type_slicing(Key, Map)]),
  NewType = join_one_key_slicing(Key, MapsLeft, lookup_type_slicing(Key, Map)),
  %io:format("NewType: ~w\n",[NewType]),
  NewAccMap = enter_type_slicing_2(Key, NewType, AccMap),
  join_maps_slicing(Left, Maps, NewAccMap);
join_maps_slicing([], _Maps, AccMap) ->
  AccMap.
     

join_one_key_slicing(Key, [Map|Maps], TypeLbl) ->
  TypeLbl2 = lookup_type_slicing(Key, Map),
  %io:format("join_one: ~w\n",[{TypeLbl,TypeLbl2}]),
  join_one_key_slicing(Key, Maps,join_one_key_slicing_(TypeLbl,TypeLbl2));
join_one_key_slicing(_Key, [], TypeLbl) ->
  TypeLbl.
  
  
join_one_key_slicing_([{Type,Lbl}|TypeLbl1],TypeLbl2)->
  %io:format("JO: ~w\n",[{Type,TypeLbl2}]),
  case t_is_any(Type) of
    true -> [{Type,Lbl}|join_one_key_slicing_(TypeLbl1,TypeLbl2)];
    false ->
      %io:format("JO: ~w\n",[{Type,TypeLbl2}]),
      TypeLbl2_=[Lbl2_ || {Type2,Lbl2_}<-TypeLbl2,Type2==Type],
      %TypeLblDifferent=[{Type2,Lbl2_} || {Type2,Lbl2_}<-TypeLbl2,Type2==Type],
      TypeLblDifferent=[{Type2,Lbl2_} || {Type2,Lbl2_}<-TypeLbl2,Type2/=Type], % CANVIE LA LINEA DE DALT XQ HEM SEMBLA MES CLAR
      case TypeLbl2_ of
		[Lbl2|_]  -> [{Type,Lbl++Lbl2}|join_one_key_slicing_(TypeLbl1,TypeLblDifferent)];
		_ -> %[{Type,Lbl}|join_one_key_slicing_(TypeLbl1,TypeLbl2)]
		     TypeLblSup=[{t_sup(Type, Type2),Lbl2_++Lbl} || {Type2,Lbl2_}<-TypeLbl2], % CONVINE ELS TIPOS
		     join_one_key_slicing_(TypeLbl1,TypeLblSup)
      end
  end;
join_one_key_slicing_([],TypeLbl) -> TypeLbl. 
 
%lookup_type_list_slicing(List, Map) ->
%  [lookup_type_slicing(X, Map) || X <- List]. 

  
lookup_type_slicing(Key, Map) ->
  case dict:find(Key, Map) of
    error -> [];
    {ok, Val} -> Val
  end.

%% ============================================================================
%%
%%  Maps and types.
%%
%% ============================================================================

join_maps(Maps) ->
  Keys = lists:foldl(fun(TmpMap, AccKeys) ->
			 [Key || Key <- AccKeys, dict:is_key(Key, TmpMap)]
		     end,
		     dict:fetch_keys(hd(Maps)), tl(Maps)),
  join_maps(Keys, Maps, dict:new()).

join_maps([Key|Left], Maps = [Map|MapsLeft], AccMap) ->
  NewType = join_one_key(Key, MapsLeft, lookup_type(Key, Map)),
  NewAccMap = enter_type(Key, NewType, AccMap),
  join_maps(Left, Maps, NewAccMap);
join_maps([], _Maps, AccMap) ->
  AccMap.

join_one_key(Key, [Map|Maps], Type) ->
  case t_is_any(Type) of
    true -> Type;
    false ->
      NewType = lookup_type(Key, Map),
      case t_is_equal(NewType, Type) of
		true  -> join_one_key(Key, Maps, Type);
		false -> join_one_key(Key, Maps, t_sup(NewType, Type))
      end
  end;
join_one_key(_Key, [], Type) ->
  Type.

maps_are_equal(Map1, Map2, Deps) ->
  NewDeps = prune_keys(Map1, Map2, Deps),
  maps_are_equal_1(Map1, Map2, NewDeps).

maps_are_equal_1(Map1, Map2, [H|Tail]) ->
  T1 = lookup_type(H, Map1),
  T2 = lookup_type(H, Map2),
  case t_is_equal(T1, T2) of
    true -> maps_are_equal_1(Map1, Map2, Tail);
    false ->
      ?debug("~w: ~s =/= ~s\n", [H, format_type(T1), format_type(T2)]),
      false
  end;
maps_are_equal_1(_Map1, _Map2, []) ->
  true.

-define(PRUNE_LIMIT, 100).

prune_keys(Map1, Map2, Deps) ->
  %% This is only worthwhile if the number of deps is reasonably large,
  %% and also bigger than the number of elements in the maps.
  NofDeps = length(Deps),
  case NofDeps > ?PRUNE_LIMIT of
    true ->
      Keys1 = dict:fetch_keys(Map1),
      case length(Keys1) > NofDeps of
	true ->
	  Set1 = lists:sort(Keys1),
	  Set2 = lists:sort(dict:fetch_keys(Map2)),
	  ordsets:intersection(ordsets:union(Set1, Set2), Deps);
	false ->
	  Deps
      end;
    false ->
      Deps
  end.

enter_type(Key, Val, Map) when is_integer(Key) ->
  ?debug("Entering ~s :: ~s\n", [format_type(t_var(Key)), format_type(Val)]),
  case t_is_any(Val) of
    true ->
      dict:erase(Key, Map);
    false ->
      LimitedVal = t_limit(Val, ?INTERNAL_TYPE_LIMIT),
      case dict:find(Key, Map) of
		{ok, LimitedVal} -> Map;
		{ok, _} -> dict:store(Key, LimitedVal, Map);
		error -> dict:store(Key, LimitedVal, Map)
      end
  end;
enter_type(Key, Val, Map) ->
  ?debug("Entering ~s :: ~s\n", [format_type(Key), format_type(Val)]),
  KeyName = t_var_name(Key),
  case t_is_any(Val) of
    true ->
      dict:erase(KeyName, Map);
    false ->
      LimitedVal = t_limit(Val, ?INTERNAL_TYPE_LIMIT),
      case dict:find(KeyName, Map) of
		{ok, LimitedVal} -> Map;
		{ok, _} -> dict:store(KeyName, LimitedVal, Map);
		error -> dict:store(KeyName, LimitedVal, Map)
      end
  end.

enter_type_lists([Key|KeyTail], [Val|ValTail], Map) ->
  Map1 = enter_type(Key, Val, Map),
  enter_type_lists(KeyTail, ValTail, Map1);
enter_type_lists([], [], Map) ->
  Map.

enter_type_list([{Key, Val}|Tail], Map) ->
  Map1 = enter_type(Key, Val, Map),
  enter_type_list(Tail, Map1);
enter_type_list([], Map) ->
  Map.
  
lookup_type_list(List, Map) ->
  [lookup_type(X, Map) || X <- List].

unsafe_lookup_type(Key, Map) ->
  case dict:find(t_var_name(Key), Map) of
    {ok, Type} -> Type;
    error -> t_none()
  end.

unsafe_lookup_type_list(List, Map) ->
  [unsafe_lookup_type(X, Map) || X <- List].

lookup_type(Key, Map) when is_integer(Key) ->
  case dict:find(Key, Map) of
    error -> t_any();
    {ok, Val} -> Val
  end;
lookup_type(#fun_var{'fun' = Fun}, Map) ->
  Fun(Map);
lookup_type(Key, Map) ->
  %% Seems unused and dialyzer complains about it -- commented out.
  %% case cerl:is_literal(Key) of
  %%   true -> t_from_term(cerl:concrete(Key));
  %%   false ->
  Subst = t_subst(Key, Map),
  t_sup(Subst, Subst).
  %% end.

mk_var(Var) ->
  case cerl:is_literal(Var) of
    true -> Var;
    false ->
      case cerl:is_c_values(Var) of
	true -> t_product(mk_var_no_lit_list(cerl:values_es(Var)));
	false -> t_var(cerl_trees:get_label(Var))
      end
  end.

mk_var_list(List) ->
  [mk_var(X) || X <- List].

mk_var_no_lit(Var) ->
  case cerl:is_literal(Var) of
    true -> t_from_term(cerl:concrete(Var));
    false -> mk_var(Var)
  end.

mk_var_no_lit_list(List) ->
  [mk_var_no_lit(X) || X <- List].

%% ============================================================================
%%
%%  The State.
%%
%% ============================================================================

new_state(SCC0, NextLabel, CallGraph, Plt, PropTypes,FunLbl) ->
  NameMap = dict:from_list([{MFA, Var} || {MFA, {Var, _Fun}, _Rec} <- SCC0]),
  SCC = [mk_var(Fun) || {_MFA, {_Var, Fun}, _Rec} <- SCC0],
  #state{callgraph = CallGraph, name_map = NameMap, next_label = NextLabel,
	 prop_types = PropTypes, plt = Plt, scc = ordsets:from_list(SCC), fun_lbl = FunLbl}.

state__set_rec_dict(State, RecDict) ->
  State#state{records = RecDict}.

state__set_opaques(#state{records = RecDict} = State, {M, _F, _A}) ->
  Opaques =
    erl_types:module_builtin_opaques(M) ++ t_opaque_from_records(RecDict),
  State#state{opaques = Opaques, module = M}.

state__lookup_record(#state{records = Records}, Tag, Arity) ->
  case erl_types:lookup_record(Tag, Arity, Records) of
    {ok, Fields} ->
      {ok, t_tuple([t_from_term(Tag)|
		    [FieldType || {_FieldName, FieldType} <- Fields]])};
    error ->
      error
  end.

state__set_in_match(State, Bool) ->
  State#state{in_match = Bool}.

state__is_in_match(#state{in_match = Bool}) ->
  Bool.

state__set_in_guard(State, Bool) ->
  State#state{in_guard = Bool}.

state__is_in_guard(#state{in_guard = Bool}) ->
  Bool.

state__get_fun_prototype(Op, Arity, State) ->
  case t_is_fun(Op) of
    true -> {State, Op};
    false ->
      {State1, [Ret|Args]} = state__mk_vars(Arity+1, State),
      Fun = t_fun(Args, Ret),
      {State1, Fun}
  end.

state__lookup_rec_var_in_scope(MFA, #state{name_map = NameMap}) ->
  dict:find(MFA, NameMap).

state__store_fun_arity(Tree, #state{fun_arities = Map} = State) ->
  Arity = length(cerl:fun_vars(Tree)),
  Id = mk_var(Tree),
  State#state{fun_arities = dict:store(Id, Arity, Map)}.

state__fun_arity(Id, #state{fun_arities = Map}) ->
  dict:fetch(Id, Map).

state__lookup_undef_var(Tree, #state{callgraph = CG, plt = Plt}) ->
  Label = cerl_trees:get_label(Tree),
  case dialyzer_callgraph:lookup_rec_var(Label, CG) of
    error -> error;
    {ok, MFA} ->
      case dialyzer_plt:lookup(Plt, MFA) of
	none -> error;
	{value, {RetType, ArgTypes}} -> {ok, t_fun(ArgTypes, RetType)}
      end
  end.

state__lookup_apply(Tree, #state{callgraph = Callgraph}) ->
  Apply = cerl_trees:get_label(Tree),
  case dialyzer_callgraph:lookup_call_site(Apply, Callgraph) of
    error ->
      unknown;
    {ok, List} ->
      case lists:member(external, List) of
	true -> unknown;
	false -> List
      end
  end.

get_apply_constr(FunType, FunLabels, Dst, ArgTypes,LblDst,LblArgTypes, 
                 #state{callgraph = CG, fun_lbl = DictFunLbl, var_lbl = VarLbl0} = State) ->
  MFAs = [dialyzer_callgraph:lookup_name(Label, CG) || Label <- FunLabels],
  %io:format("\nDictFunLbl:~p\n",[dict:to_list(DictFunLbl)]),
  %io:format("\n\n\n\nENTRA: ~p ~w\n~w ~w\n~w ~w\n\n\n",[MFAs,FunLabels, ArgTypes,LblArgTypes,Dst,LblDst]),
  case lists:member(error, MFAs) of
    true -> 
      DictPending = lists:flatten([build_pending_labels(Label,[Dst |ArgTypes]) || Label <- FunLabels]),
      DictPending_ = lists:flatten([build_pending_labels(Label,[t_fun_range(FunType) |t_fun_args(FunType)]) || Label <- FunLabels]),
      %io:format("DictPending: ~p\n",[DictPending]),
      DictLblFunPending_ = dict:merge(fun(_,V1,V2)-> V1++V2 end,
                                     dict:from_list(DictPending),
                                     VarLbl0),
      DictLblFunPending = dict:merge(fun(_,V1,V2)-> V1++V2 end,
                               dict:from_list(DictPending_),
                               DictLblFunPending_),
      State1 = State#state{var_lbl = DictLblFunPending},
      {error,State1};
    false ->
      LblFun = [{MFA,case dict:find(MFA,DictFunLbl) of
		        {ok,LblFun} -> LblFun;
		        error -> [[] || _ <- [Dst |ArgTypes] ]
		   end} || {ok, MFA} <- MFAs],
      ConstrList = [begin
		   State1 = state__new_constraint_context_slicing(State),
		   State2 = get_plt_constr(MFA, Dst, ArgTypes, State1),
		   {state__cs(State2),{MFA,state__cs_slicing(State2)}}
		 end || {ok, MFA} <- MFAs],
      {Constrs,ConstrsSlicing}=lists:unzip(ConstrList),
      %io:format("\n\n\n\nENTRA: ~p\n\n\n\n",[{ConstrsSlicing,ArgTypes,Dst}]),
      ApplyConstr = mk_disj_constraint_list(Constrs),
      NConstrsSlicing_ =
        [begin
            [LblFDst_ | LblFArgs__] = lists:reverse(LblF),
            LblFArgs_ = lists:reverse(LblFArgs__),
            %io:format("LblFDst:~w\nLblFArgs:~w\n",[LblFDst,LblFArgs]),
            %{_,LblFArgsLbl} = lists:unzip(LblFArgs),
            DictArgs = dict:from_list(lists:zip(ArgTypes,LblArgTypes)),
            DictDst = dict:from_list([{Dst,LblDst}]),
            DictLbl = dict:merge(fun(_,V1,V2)-> V1++V2 end,DictArgs,DictDst),
%            io:format("\n\n\n\LblFArgs_: ~w\nLblArgTypes: ~w\nLblFDst: ~w\nLblDst: ~w\n\n\n\n",
%                      [LblFArgs_,LblArgTypes,LblFDst_,LblDst]),
            %LblFArgs = append_list(LblFArgs_,LblArgTypes),
            LblF_ = [LblFDst_ | LblFArgs_],
            Lbl_ = [LblDst | LblArgTypes],
            [LblFDst|LblFArgs] = append_type_list(LblF_,Lbl_),
            %LblFArgs = [[] || _ <-ArgTypes],		
            {{constraint_list_slicing,conj,put_labels_apply(ListCtrs,DictLbl),Deps,Id},
              lists:zip(ArgTypes,LblFArgs)++lists:zip(t_fun_args(FunType),LblFArgs)
              ++[{Dst,LblFDst},{t_fun_range(FunType),LblFDst}]}
          end||
         {MFA,{constraint_list_slicing,conj,ListCtrs,Deps,Id}} <- ConstrsSlicing,
         {MFA_,LblF} <- LblFun, MFA == MFA_],
      {NConstrsSlicing,DictLblFun_} = lists:unzip(NConstrsSlicing_),
      %DictLblFun = dict:merge(fun(_,V1,V2)-> V1++V2 end,dict:from_list(lists:flatten(DictLblFun_)),VarLbl0),
      DictLblFun = dict:merge(fun discard_repeated/3,dict:from_list(lists:flatten(DictLblFun_)),VarLbl0),
      %DictLblFun = dict:merge(fun(_,V1,_)-> V1 end,dict:from_list(lists:flatten(DictLblFun_)),VarLbl0),
      %DictLblFun = dict:new(),
      State1 = State#state{var_lbl = DictLblFun},
      %io:format("Modifica var_lbl:~w\n",[dict:to_list(DictLblFun)]),
      State2 = State1,
      %State2 = State#state{ctrs_lbl = DictCtrs},
      ApplyConstrSlicing = mk_disj_constraint_list(NConstrsSlicing),
      LastState = state__store_conj(ApplyConstr, State2),
      {ok, state__store_conj_slicing(ApplyConstrSlicing, LastState)}
  end.
  
discard_repeated(_,[{Type,Lbls}|VarLbl1],VarLbl2)->
   case [Type2 || {Type2,_}<-VarLbl2,Type2==Type] of
        [] -> [{Type,Lbls} | discard_repeated(0,VarLbl1,VarLbl2)];
        _ -> discard_repeated(0,VarLbl1,VarLbl2)
   end;
discard_repeated(_,[],VarLbl2)->
   VarLbl2.

put_labels_apply([{constraint_slicing,{constraint,T1,Op,T2,Dep},_}|Tail],Dict)->
        Lbl1 =
	   case dict:find(T1,Dict) of
	        {ok,Lbl1_} -> Lbl1_;
	        error -> []
	   end,
	Lbl2 =
	   case dict:find(T2,Dict) of
	        {ok,Lbl2_} -> Lbl2_;
	        error -> []
	   end,
	C = {constraint_slicing,{constraint,T1,Op,T2,Dep},Lbl1++Lbl2},
	[C | put_labels_apply(Tail,Dict)];
put_labels_apply([],_) -> [].

build_pending_labels(Label,List) ->
   build_pending_labels(Label,List,1).
 
build_pending_labels(Label,[H|T],N)-> 
  [{H,[{pending,Label,N}]} | build_pending_labels(Label,T,N+1)];
build_pending_labels(_,[],_) -> [].

append_type_list([H1|T1],[H2|T2])->
   [ [{Type,Lbl++H2}||{Type,Lbl}<-H1]
     |append_type_list(T1,T2)];
append_type_list(L=[_|_],[])->L;
append_type_list([],_)->[].


state__scc(#state{scc = SCC}) ->
  SCC.

state__add_fun_to_scc(Fun, #state{scc = SCC} = State) ->
  State#state{scc = ordsets:add_element(Fun, SCC)}.

state__plt(#state{plt = PLT}) ->
  PLT.

state__new_constraint_context(State) ->
  State#state{cs = []}.

state__new_constraint_context_slicing(State) ->
  State1 = state__new_constraint_context(State),
  State1#state{cs_slicing = []}.

state__prop_domain(FunLabel, #state{prop_types = PropTypes}) ->
 case dict:find(FunLabel, PropTypes) of
    error -> error;
    {ok, {_Range_Fun, Dom}} -> {ok, Dom};
    {ok, FunType} -> {ok, t_fun_args(FunType)}
  end.

state__add_prop_constrs(Tree, #state{prop_types = PropTypes} = State) ->
  Label = cerl_trees:get_label(Tree),
  case dict:find(Label, PropTypes) of
    error -> State;
    {ok, FunType} ->
      case t_fun_args(FunType) of
	unknown -> State;
	ArgTypes ->
	  case erl_types:any_none(ArgTypes) of
	    true -> not_called;
	    false ->
	      ?debug("Adding propagated constr: ~s for function ~w\n",
		     [format_type(FunType), debug_lookup_name(mk_var(Tree))]),
	      FunVar = mk_var(Tree),
	      state__store_conj_slicing(FunVar, sub, FunType, [cerl_trees_:get_label(Tree)], State)
	  end
      end
  end.
  


state__cs(#state{cs = Cs}) ->
  mk_conj_constraint_list(Cs).
  
state__cs_slicing(#state{cs_slicing = Cs}) ->
  mk_conj_constraint_list_slicing(Cs).

state__store_conj(C, #state{cs = Cs} = State) ->
  State#state{cs = [C|Cs]}.
  
state__store_conj_slicing(C, #state{cs_slicing = Cs} = State) ->
  State#state{cs_slicing = [C|Cs]}.

state__store_conj_list([H|T], State) ->
 %io:format("H: ~p\n",[H]),
  State1 = state__store_conj(H, State),
  state__store_conj_list(T, State1);
state__store_conj_list([], State) ->
  State.
  
state__store_conj_list_slicing([H|T], State) ->
  State1 = state__store_conj_slicing(H, State),
  state__store_conj_list_slicing(T, State1);
state__store_conj_list_slicing([], State) ->
  State.

state__store_conj(Lhs, Op, Rhs, #state{cs = Cs} = State) ->
  State#state{cs = [mk_constraint(Lhs, Op, Rhs)|Cs]}.
  
state__store_conj_slicing(Lhs, Op, Rhs,Lbl, #state{cs_slicing = Cs} = State) ->
  State1 = state__store_conj(Lhs, Op, Rhs, State),
  State1#state{cs_slicing = [mk_constraint_slicing(Lhs, Op, Rhs,Lbl)|Cs]}.

state__store_conj_lists(List1, Op, List2, State) ->
  {NewList1, NewList2} = strip_of_any_constrs(List1, List2),
  state__store_conj_lists_1(NewList1, Op, NewList2, State).
       
state__store_conj_lists_slicing(List1, Op, List2,Lbl, Lbls, State) ->
  State1 = state__store_conj_lists(List1, Op, List2, State),
  {NewList1, NewList2} = strip_of_any_constrs(List1, List2),
  state__store_conj_lists_slicing_1(NewList1, Op, NewList2, Lbl,lists:reverse(Lbls), State1).

strip_of_any_constrs(List1, List2) ->
  strip_of_any_constrs(List1, List2, [], []).

strip_of_any_constrs([T1|Left1], [T2|Left2], Acc1, Acc2) ->
  case t_is_any(T1) orelse constraint_opnd_is_any(T2) of
    true -> strip_of_any_constrs(Left1, Left2, Acc1, Acc2);
    false -> strip_of_any_constrs(Left1, Left2, [T1|Acc1], [T2|Acc2])
  end;
strip_of_any_constrs([], [], Acc1, Acc2) ->
  {Acc1, Acc2}.

state__store_conj_lists_1([Arg1|Arg1Tail], Op, [Arg2|Arg2Tail], State) ->
  State1 = state__store_conj(Arg1, Op, Arg2, State),
  state__store_conj_lists_1(Arg1Tail, Op, Arg2Tail, State1);
state__store_conj_lists_1([], _Op, [], State) ->
  State.
  
state__store_conj_lists_slicing_1([Arg1|Arg1Tail], Op, [Arg2|Arg2Tail], CommonLbl, [Lbl|LblTail], State) ->
  %io:format("Arg1: ~w\nArg2: ~w\nLbl: ~w\n",[Arg1,Arg2,Lbl]),
  State1 = state__store_conj_slicing(Arg1, Op, Arg2,Lbl++CommonLbl, State),
  state__store_conj_lists_slicing_1(Arg1Tail, Op, Arg2Tail, CommonLbl, LblTail, State1);
state__store_conj_lists_slicing_1([], _Op, [], _Lbl, _Lbls, State) ->
  State.

state__mk_var(#state{next_label = NL} = State) ->
  {State#state{next_label = NL+1}, t_var(NL)}.

state__mk_vars(N, #state{next_label = NL} = State) ->
  NewLabel = NL + N,
  Vars = [t_var(X) || X <- lists:seq(NL, NewLabel-1)],
  {State#state{next_label = NewLabel}, Vars}.

state__store_constrs(Id, Cs, #state{cmap = Dict} = State) ->
  NewDict = dict:store(Id, Cs, Dict),
  State#state{cmap = NewDict}.
  
state__store_constrs_slicing(Id, Cs, Cs_slicing, #state{cmap_slicing = Dict} = State) ->
  State1 = state__store_constrs(Id, Cs, State),
  NewDict = dict:store(Id, Cs_slicing, Dict),
  State1#state{cmap_slicing = NewDict}.

state__get_cs(Var, #state{cmap = Dict}) ->
  dict:fetch(Var, Dict).
  
state__get_cs_slicing(Var, #state{cmap_slicing = Dict}) ->
  dict:fetch(Var, Dict).

%% The functions here will not be treated as self recursive.
%% These functions will need to be handled as such manually.
state__mark_as_non_self_rec(SCC, #state{non_self_recs = NS} = State) ->
  State#state{non_self_recs = ordsets:union(NS, ordsets:from_list(SCC))}.

state__is_self_rec(Fun, #state{callgraph = CallGraph, non_self_recs = NS}) ->
  case ordsets:is_element(Fun, NS) of
    true -> false;
    false -> dialyzer_callgraph:is_self_rec(t_var_name(Fun), CallGraph)
  end.

state__store_funs(Vars0, Funs0, #state{fun_map = Map} = State) ->
  debug_make_name_map(Vars0, Funs0),
  Vars = mk_var_list(Vars0),
  Funs = mk_var_list(Funs0),
  NewMap = lists:foldl(fun({Var, Fun}, MP) -> orddict:store(Var, Fun, MP) end,
		       Map, lists:zip(Vars, Funs)),
  State#state{fun_map = NewMap}.

state__get_rec_var(Fun, #state{fun_map = Map}) ->
  case [V || {V, FV} <- Map, FV =:= Fun] of
    [Var] -> {ok, Var};
    [] -> error
  end.

state__finalize(State) ->
  State1 = enumerate_constraints(State),
  order_fun_constraints(State1).

%% ============================================================================
%%
%%  Constraints
%%
%% ============================================================================

-spec mk_constraint(erl_types:erl_type(), constr_op(), fvar_or_type()) -> #constraint{}.

mk_constraint(Lhs, Op, Rhs) ->
  case t_is_any(Lhs) orelse constraint_opnd_is_any(Rhs) of
    false ->
      Deps = find_constraint_deps([Lhs, Rhs]),
      C0 = mk_constraint_1(Lhs, Op, Rhs),
      C = C0#constraint{deps = Deps},
      case Deps =:= [] of
	true ->
	  %% This constraint is constant. Solve it immediately.
	  case solve_one_c(C, dict:new(), []) of
	    error -> throw(error);
	    _ ->
	      %% This is always true, keep it anyway for logistic reasons
	      C
	  end;
	false ->
	  C
      end;
    true ->
      C = mk_constraint_1(t_any(), Op, t_any()),
      C#constraint{deps = []}
  end.
  
  
mk_constraint_slicing(Lhs, Op, Rhs,Lbl) ->
  C=mk_constraint(Lhs, Op, Rhs),
  #constraint_slicing{cs=C,lbls= Lbl}.

%% the following function is used so that we do not call
%% erl_types:t_is_any/1 with a term other than an erl_type()
-spec constraint_opnd_is_any(fvar_or_type()) -> boolean().

constraint_opnd_is_any(#fun_var{}) -> false;
constraint_opnd_is_any(Type) -> t_is_any(Type).

-spec mk_fun_var(fun((_) -> erl_types:erl_type()), [erl_types:erl_type()]) -> #fun_var{}.

mk_fun_var(Fun, Types) ->
  Deps = [t_var_name(Var) || Var <- t_collect_vars(t_product(Types))],
  #fun_var{'fun' = Fun, deps = ordsets:from_list(Deps)}.

-spec get_deps(constr()) -> [dep()].

get_deps(#constraint{deps = D}) -> D;
get_deps(#constraint_list{deps = D}) -> D;
get_deps(#constraint_ref{deps = D}) -> D.


-spec get_deps_slicing(constr_slicing()) -> [dep()].

get_deps_slicing(#constraint_slicing{cs = C}) -> get_deps(C);
get_deps_slicing(#constraint_list_slicing{deps = D}) -> D;
get_deps_slicing(#constraint_ref{deps = D}) -> D.

-spec find_constraint_deps([fvar_or_type()]) -> [dep()].

find_constraint_deps(List) ->
  ordsets:from_list(find_constraint_deps(List, [])).

find_constraint_deps([#fun_var{deps = Deps}|Tail], Acc) ->
  find_constraint_deps(Tail, [Deps|Acc]);
find_constraint_deps([Type|Tail], Acc) ->
  NewAcc = [[t_var_name(D) || D <- t_collect_vars(Type)]|Acc],
  find_constraint_deps(Tail, NewAcc);
find_constraint_deps([], Acc) ->
  lists:flatten(Acc).

mk_constraint_1(Lhs, eq, Rhs) when Lhs < Rhs ->
  #constraint{lhs = Lhs, op = eq, rhs = Rhs};
mk_constraint_1(Lhs, eq, Rhs) ->
  #constraint{lhs = Rhs, op = eq, rhs = Lhs};
mk_constraint_1(Lhs, Op, Rhs) ->
  #constraint{lhs = Lhs, op = Op, rhs = Rhs}.

mk_constraints([Lhs|LhsTail], Op, [Rhs|RhsTail]) ->
  [mk_constraint(Lhs, Op, Rhs)|mk_constraints(LhsTail, Op, RhsTail)];
mk_constraints([], _Op, []) ->
  [].

mk_constraint_ref(Id, Deps) ->
  #constraint_ref{id = Id, deps = Deps}.

mk_constraint_list(Type, List) ->
  %List1 = ordsets:from_list(lift_lists(Type, List)),
  %List2 = ordsets:filter(fun(X) -> get_deps(X) =/= [] end, List1),
  List1 = lift_lists(Type, List),
  List2 = lists:filter(fun(X) -> get_deps(X) =/= [] end, List1),
  Deps = calculate_deps(List2),
  case Deps =:= [] of
    true -> #constraint_list{type = conj,
			     list = [mk_constraint(t_any(), eq, t_any())],
			     deps = []};
    false -> #constraint_list{type = Type, list = List2, deps = Deps}
  end.
  
mk_constraint_list_slicing(Type, List) ->
  %List1 = ordsets:from_list(lift_lists(Type, List)),
  %List2 = ordsets:filter(fun(X) -> get_deps_slicing(X) =/= [] end, List1),
  List1 = lift_lists(Type, List),
  List2 = lists:filter(fun(X) -> get_deps_slicing(X) =/= [] end, List1),
  Deps = calculate_deps_slicing(List2),
  case Deps =:= [] of
    true -> #constraint_list_slicing{type = conj,
			     list = [mk_constraint_slicing(t_any(), eq, t_any(),[])],
			     deps = []};
    false -> #constraint_list_slicing{type = Type, list = List2, deps = Deps}
  end.

lift_lists(Type, List) ->
  lift_lists(Type, List, []).

lift_lists(Type, [#constraint_list{type = Type, list = List}|Tail], Acc) ->
  lift_lists(Type, Tail, List++Acc);
lift_lists(Type, [#constraint_list_slicing{type = Type, list = List}|Tail], Acc) ->
  lift_lists(Type, Tail, List++Acc);
lift_lists(Type, [C|Tail], Acc) ->
  lift_lists(Type, Tail, [C|Acc]);
lift_lists(_Type, [], Acc) ->
  Acc.

update_constraint_list(CL, List) ->
  CL#constraint_list{list = List}.

%% We expand guard constraints into dijunctive normal form to gain
%% precision in simple guards. However, because of the exponential
%% growth of this expansion in the presens of disjunctions we can even
%% get into trouble while expanding.
%%
%% To limit this we only expand when the number of disjunctions are
%% below a certain limit. This limit is currently set based on the
%% behaviour of boolean 'or'.
%%
%%         V1 = V2 or V3
%%
%% Gives us in simplified form the constraints
%%
%%         <Some cs> * ((V1 = true) + (V2 = true) + (V1 = false))
%%
%% and thus a three-parted disjunction. If want to allow for two
%% levels of disjunction we need to have 3^2 = 9 disjunctions. If we
%% want three levels we need 3^3 = 27 disjunctions. More than that
%% seems unnecessary and tends to blow up.
%%
%% Note that by not expanding we lose some precision, but we get a
%% safe over approximation.

-define(DISJ_NORM_FORM_LIMIT, 28).

mk_disj_norm_form(#constraint_list{} = CL) ->
  try
    List1 = expand_to_conjunctions(CL),
    mk_disj_constraint_list(List1)
  catch
    throw:too_many_disj -> CL
  end.
  
mk_disj_norm_form_slicing(#constraint_list_slicing{} = CL) ->
  try
    List1 = expand_to_conjunctions_slicing(CL),
    mk_disj_constraint_list_slicing(List1)
  catch
    throw:too_many_disj -> CL
  end.

expand_to_conjunctions(#constraint_list{type = conj, list = List}) ->
  List1 = [C || C <- List, is_simple_constraint(C)],
  List2 = [expand_to_conjunctions(C) || #constraint_list{} = C <- List],
  case List2 =:= [] of
    true -> [mk_conj_constraint_list(List1)];
    false ->
      case List2 of
	[JustOneList] ->
	  [mk_conj_constraint_list([L|List1]) || L <- JustOneList];
	_ ->
	  combine_conj_lists(List2, List1)
      end
  end;
expand_to_conjunctions(#constraint_list{type = disj, list = List}) ->
  if length(List) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ok
  end,
  List1 = [C || C <- List, is_simple_constraint(C)],
  %% Just an assert.
  [] = [C || #constraint{} = C <- List1],
  Expanded = lists:flatten([expand_to_conjunctions(C)
			    || #constraint_list{} = C <- List]),
  ReturnList = Expanded ++ List1,
  if length(ReturnList) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ReturnList
  end.
  
expand_to_conjunctions_slicing(#constraint_list_slicing{type = conj, list = List}) ->
  List1 = [C || C <- List, is_simple_constraint_slicing(C)],
  List2 = [expand_to_conjunctions(C) || #constraint_list_slicing{} = C <- List],
  case List2 =:= [] of
    true -> [mk_conj_constraint_list_slicing(List1)];
    false ->
      case List2 of
	[JustOneList] ->
	  [mk_conj_constraint_list_slicing([L|List1]) || L <- JustOneList];
	_ ->
	  combine_conj_lists_slicing(List2, List1)
      end
  end;
expand_to_conjunctions_slicing(#constraint_list_slicing{type = disj, list = List}) ->
  if length(List) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ok
  end,
  List1 = [C || C <- List, is_simple_constraint_slicing(C)],
  %% Just an assert.
  [] = [C || #constraint_slicing{} = C <- List1],
  Expanded = lists:flatten([expand_to_conjunctions_slicing(C)
			    || #constraint_list_slicing{} = C <- List]),
  ReturnList = Expanded ++ List1,
  if length(ReturnList) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ReturnList
  end.

is_simple_constraint(#constraint{}) -> true;
is_simple_constraint(#constraint_ref{}) -> true;
is_simple_constraint(#constraint_list{}) -> false.

is_simple_constraint_slicing(#constraint_slicing{}) -> true;
is_simple_constraint_slicing(#constraint_ref{}) -> true;
is_simple_constraint_slicing(#constraint_list_slicing{}) -> false.

combine_conj_lists([List1, List2|Left], Prefix) ->
  NewList = [mk_conj_constraint_list([L1, L2]) || L1 <- List1, L2 <- List2],
  if length(NewList) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ok
  end,
  combine_conj_lists([NewList|Left], Prefix);
combine_conj_lists([List], Prefix) ->
  [mk_conj_constraint_list([mk_conj_constraint_list(Prefix), L]) || L <- List].
  
combine_conj_lists_slicing([List1, List2|Left], Prefix) ->
  NewList = [mk_conj_constraint_list_slicing([L1, L2]) || L1 <- List1, L2 <- List2],
  if length(NewList) > ?DISJ_NORM_FORM_LIMIT -> throw(too_many_disj);
     true -> ok
  end,
  combine_conj_lists_slicing([NewList|Left], Prefix);
combine_conj_lists_slicing([List], Prefix) ->
  [mk_conj_constraint_list_slicing([mk_conj_constraint_list_slicing(Prefix), L]) || L <- List].

calculate_deps(List) ->
  calculate_deps(List, []).

calculate_deps([H|Tail], Acc) ->
  Deps = get_deps(H),
  calculate_deps(Tail, [Deps|Acc]);
calculate_deps([], Acc) ->
  ordsets:from_list(lists:flatten(Acc)).


calculate_deps_slicing(List) ->
  calculate_deps_slicing(List, []).

calculate_deps_slicing([H|Tail], Acc) ->
  Deps = get_deps_slicing(H),
  calculate_deps_slicing(Tail, [Deps|Acc]);
calculate_deps_slicing([], Acc) ->
  ordsets:from_list(lists:flatten(Acc)).


mk_conj_constraint_list(List) ->
  mk_constraint_list(conj, List).
  
  
mk_conj_constraint_list_slicing(List) ->
  mk_constraint_list_slicing(conj, List).

mk_disj_constraint_list([NotReallyAList]) ->
  NotReallyAList;
mk_disj_constraint_list(List) ->
  %% Make sure each element in the list is either a conjunction or a
  %% ref. Wrap single constraints into conjunctions.
  List1 = [wrap_simple_constr(C) || C <- List],
  mk_constraint_list(disj, List1).
  
mk_disj_constraint_list_slicing([NotReallyAList]) ->
  NotReallyAList;
mk_disj_constraint_list_slicing(List) ->
  %% Make sure each element in the list is either a conjunction or a
  %% ref. Wrap single constraints into conjunctions.
  List1 = [wrap_simple_constr_slicing(C) || C <- List],
  mk_constraint_list_slicing(disj, List1).

wrap_simple_constr(#constraint{} = C) -> mk_conj_constraint_list([C]);
wrap_simple_constr(#constraint_list{} = C) -> C;
wrap_simple_constr(#constraint_ref{} = C) -> C.

wrap_simple_constr_slicing(#constraint_slicing{} = C) -> mk_conj_constraint_list_slicing([C]);
wrap_simple_constr_slicing(#constraint_list_slicing{} = C) -> C;
wrap_simple_constr_slicing(#constraint_ref{} = C) -> C.

enumerate_constraints(State) ->
  Cs = [mk_constraint_ref(Id, get_deps(state__get_cs(Id, State)))
	|| Id <- state__scc(State)],
  {_, _, NewState} = enumerate_constraints(Cs, 0, [], State),
  NewState.

enumerate_constraints([#constraint_ref{id = Id} = C|Tail], N, Acc, State) ->
  Cs = state__get_cs(Id, State),
  {[NewCs], NewN, NewState1} = enumerate_constraints([Cs], N, [], State),
  NewState2 = state__store_constrs(Id, NewCs, NewState1),
  enumerate_constraints(Tail, NewN+1, [C|Acc], NewState2);
enumerate_constraints([#constraint_list{type = conj, list = List} = C|Tail],
		      N, Acc, State) ->
  %% Separate the flat constraints from the deep ones to make a
  %% separate fixpoint interation over the flat ones for speed.
  {Flat, Deep} = lists:splitwith(fun(#constraint{}) -> true;
				    (#constraint_list{}) -> false;
				    (#constraint_ref{}) -> false
				 end, List),
  {NewFlat, N1, State1} = enumerate_constraints(Flat, N, [], State),
  {NewDeep, N2, State2} = enumerate_constraints(Deep, N1, [], State1),
  {NewList, N3} =
    case shorter_than_two(NewFlat) orelse (NewDeep =:= []) of
      true -> {NewFlat ++ NewDeep, N2};
      false ->
	{NewCLists, TmpN} = group_constraints_in_components(NewFlat, N2),
	{NewCLists ++ NewDeep, TmpN}
    end,
  NewAcc = [C#constraint_list{list = NewList, id = {list, N3}}|Acc],
  enumerate_constraints(Tail, N3+1, NewAcc, State2);
enumerate_constraints([#constraint_list{list = List, type = disj} = C|Tail],
		      N, Acc, State) ->
  {NewList, NewN, NewState} = enumerate_constraints(List, N, [], State),
  NewAcc = [C#constraint_list{list = NewList, id = {list, NewN}}|Acc],
  enumerate_constraints(Tail, NewN+1, NewAcc, NewState);
enumerate_constraints([#constraint{} = C|Tail], N, Acc, State) ->
  enumerate_constraints(Tail, N, [C|Acc], State);
enumerate_constraints([], N, Acc, State) ->
  {lists:reverse(Acc), N, State}.

shorter_than_two([]) -> true;
shorter_than_two([_]) -> true;
shorter_than_two([_|_]) -> false.

group_constraints_in_components(Cs, N) ->
  DepList = [Deps || #constraint{deps = Deps} <- Cs],
  case find_dep_components(DepList, []) of
    [_] -> {Cs, N};
    [_|_] = Components ->
      ConstrComp = [[C || #constraint{deps = D} = C <- Cs,
			  ordsets:is_subset(D, Comp)]
		    || Comp <- Components],
      lists:mapfoldl(fun(CComp, TmpN) ->
			 TmpCList = mk_conj_constraint_list(CComp),
			 {TmpCList#constraint_list{id = {list, TmpN}},
			  TmpN + 1}
		     end, N, ConstrComp)
  end.

find_dep_components([Set|Left], AccComponents) ->
  {Component, Ungrouped} = find_dep_components(Left, Set, []),
  case Component =:= Set of
    true -> find_dep_components(Ungrouped, [Component|AccComponents]);
    false -> find_dep_components([Component|Ungrouped], AccComponents)
  end;
find_dep_components([], AccComponents) ->
  AccComponents.

find_dep_components([Set|Left], AccSet, Ungrouped) ->
  case ordsets:intersection(Set, AccSet) of
    [] -> find_dep_components(Left, AccSet, [Set|Ungrouped]);
    [_|_] -> find_dep_components(Left, ordsets:union(Set, AccSet), Ungrouped)
  end;
find_dep_components([], AccSet, Ungrouped) ->
  {AccSet, Ungrouped}.

%% Put the fun ref constraints last in any conjunction since we need
%% to separate the environment from the interior of the function.
order_fun_constraints(State) ->
  Cs = [mk_constraint_ref(Id, get_deps(state__get_cs(Id, State)))
	|| Id <- state__scc(State)],
  order_fun_constraints(Cs, State).

order_fun_constraints([#constraint_ref{id = Id}|Tail], State) ->
  Cs = state__get_cs(Id, State),
  {[NewCs], State1} = order_fun_constraints([Cs], [], [], State),
  NewState = state__store_constrs(Id, NewCs, State1),
  order_fun_constraints(Tail, NewState);
order_fun_constraints([], State) ->
  State.

order_fun_constraints([#constraint_ref{} = C|Tail], Funs, Acc, State) ->
  order_fun_constraints(Tail, [C|Funs], Acc, State);
order_fun_constraints([#constraint_list{list = List, type = Type} = C|Tail],
		      Funs, Acc, State) ->
  {NewList, NewState} =
    case Type of
      conj -> order_fun_constraints(List, [], [], State);
      disj ->
	FoldFun = fun(X, AccState) ->
		      {[NewX], NewAccState} =
			order_fun_constraints([X], [], [], AccState),
		      {NewX, NewAccState}
		  end,
	lists:mapfoldl(FoldFun, State, List)
    end,
  NewAcc = [update_constraint_list(C, NewList)|Acc],
  order_fun_constraints(Tail, Funs, NewAcc, NewState);
order_fun_constraints([#constraint{} = C|Tail], Funs, Acc, State) ->
  order_fun_constraints(Tail, Funs, [C|Acc], State);
order_fun_constraints([], Funs, Acc, State) ->
  NewState = order_fun_constraints(Funs, State),
  {lists:reverse(Acc)++Funs, NewState}.

%% ============================================================================
%%
%%  Utilities.
%%
%% ============================================================================

is_singleton_non_number_type(Type) ->
  case t_is_number(Type) of
    true -> false;
    false -> is_singleton_type(Type)
  end.

is_singleton_type(Type) ->
  case t_is_atom(Type) of
    true ->
      case t_atom_vals(Type) of
	unknown -> false;
	[_] -> true;
	[_|_] -> false
      end;
    false ->
      case t_is_integer(Type) of
	true ->
	  case t_number_vals(Type) of
	    unknown -> false;
	    [_] -> true;
	    [_|_] -> false
	  end;
	false ->
	  t_is_nil(Type)
      end
  end.

find_element(Args, Cs) ->
  [Pos, Tuple] = Args,
  case erl_types:t_is_number(Pos) of
    true ->
      case erl_types:t_number_vals(Pos) of
        'unknown' -> 'unknown';
        [I] ->
          case find_constraint(Tuple, Cs) of
            'unknown' -> 'unknown';
            #constraint{lhs = ExTuple} ->
              case erl_types:t_is_tuple(ExTuple) of
                true ->
                  Elems = erl_types:t_tuple_args(ExTuple),
                  Elem = lists:nth(I, Elems),
                  case erl_types:t_is_var(Elem) of
                    true -> Elem;
                    false -> 'unknown'
                  end;
                false -> 'unknown'
              end
          end;
        _ -> 'unknown'
      end;
    false -> 'unknown'
  end.

find_constraint(_Tuple, []) ->
  'unknown';
find_constraint(Tuple, [#constraint{op = 'eq', rhs = Tuple} = C|_]) ->
  C;
find_constraint(Tuple, [#constraint_list{list = List}|Cs]) ->
  find_constraint(Tuple, List ++ Cs);
find_constraint(Tuple, [_|Cs]) ->
  find_constraint(Tuple, Cs).

%% ============================================================================
%%
%%  Pretty printer and debug facilities.
%%
%% ============================================================================

-ifdef(DEBUG_CONSTRAINTS).
-ifndef(DEBUG).
-define(DEBUG, true).
-endif.
-endif.

%-ifdef(DEBUG).
%format_type(#fun_var{deps = Deps}) ->
%  io_lib:format("Fun(~s)", [lists:flatten([format_type(t_var(X))||X<-Deps])]);
%format_type(Type) ->
%  case cerl:is_literal(Type) of
%    true -> io_lib:format("~w", [cerl:concrete(Type)]);
%    false -> erl_types:t_to_string(Type)
%  end.
%-endif.

%-ifdef(DEBUG_NAME_MAP).
debug_make_name_map(Vars, Funs) ->
  Map = get(dialyzer_typesig_map),
  NewMap =
    if Map =:= undefined -> debug_make_name_map(Vars, Funs, dict:new());
       true              -> debug_make_name_map(Vars, Funs, Map)
    end,
  put(dialyzer_typesig_map, NewMap).

debug_make_name_map([Var|VarLeft], [Fun|FunLeft], Map) ->
  Name = {cerl:fname_id(Var), cerl:fname_arity(Var)},
  FunLabel = cerl_trees:get_label(Fun),
  debug_make_name_map(VarLeft, FunLeft, dict:store(FunLabel, Name, Map));
debug_make_name_map([], [], Map) ->
  Map.

%debug_lookup_name(Var) ->
%  case dict:find(t_var_name(Var), get(dialyzer_typesig_map)) of
%    error -> Var;
%    {ok, Name} -> Name
%  end.

%-else.
%debug_make_name_map(_Vars, _Funs) ->
%  ok.
%-endif.


%-ifdef(DEBUG_CONSTRAINTS).

%pp_constraints_slicing(Cs,State) ->
%  Res = pp_constraints_slicing(Cs, none, 0, 0, State),
%  io:nl(),
%  Res.	
%  
%pp_constraints_slicing([], _, _, MaxDepth,_)->MaxDepth;
%pp_constraints_slicing([C|Cs], Separator, Level, MaxDepth,
%	       State)-> 
%   NewMaxDepth_ =
%   case C of
%   	    #constraint_ref{} -> 
%   	       pp_constraints([C],Separator, Level, MaxDepth,State);
%   	    #constraint_slicing{cs = Ctrn,lbls = Lbl} ->
%   	       pp_constraints([Ctrn],Separator, Level, MaxDepth,State),
%   	       io:format(" %from ~w%", [Lbl]);
%   	    #constraint_list_slicing{type = Type, list = List, id = Id} ->
%   	         io:format("%List ~w(", [Id]),
%			 NewSeparator = case Type of
%							   conj -> "*";
%							   disj -> "+"
%							end,
%			  NewMaxDepth = pp_constraints_slicing(List, NewSeparator, Level + 1, MaxDepth, State),
%			  io:format(")", []),
%			  NewMaxDepth
%   end,
%   io:nl(),
%   pp_constraints_slicing(Cs, Separator, Level, NewMaxDepth_,State).

%pp_constrs_scc(SCC, State) ->
%  [pp_constrs(Fun, state__get_cs(Fun, State), State) || Fun <- SCC].
%
%pp_constrs(Fun, Cs, State) ->
%  io:format("Constraints for fun: ~w\n", [debug_lookup_name(Fun)]),
%  MaxDepth = pp_constraints(Cs, State),
%  io:format("Depth: ~w\n", [MaxDepth]).
%
%pp_constraints(Cs, State) ->
%  Res = pp_constraints([Cs], none, 0, 0, State),
%  io:nl(),
%  Res.

%pp_constraints([List|Tail], Separator, Level, MaxDepth,
%	       State) when is_list(List) ->
%  pp_constraints(List++Tail, Separator, Level, MaxDepth, State);
%pp_constraints([#constraint_ref{id = Id}|Left], Separator,
%	       Level, MaxDepth, State) ->
%  Cs = state__get_cs(Id, State),
%  io:format("%Ref ~w%", [t_var_name(Id)]),
%  pp_constraints([Cs|Left], Separator, Level, MaxDepth, State);
%pp_constraints([#constraint{lhs = Lhs, op = Op, rhs = Rhs}], _Separator,
%	       Level, MaxDepth, _State) ->
%  io:format("~s ~w ~s", [format_type(Lhs), Op, format_type(Rhs)]),
%  erlang:max(Level, MaxDepth);
%pp_constraints([#constraint{lhs = Lhs, op = Op, rhs = Rhs}|Tail], Separator,
%	       Level, MaxDepth, State) ->
%  io:format("~s ~w ~s ~s ", [format_type(Lhs), Op, format_type(Rhs),Separator]),
%  pp_constraints(Tail, Separator, Level, MaxDepth, State);
%pp_constraints([#constraint_list{type = Type, list = List, id = Id}],
%	       _Separator, Level, MaxDepth, State) ->
%  io:format("%List ~w(", [Id]),
%  NewSeparator = case Type of
%		   conj -> "*";
%		   disj -> "+"
%		 end,
%  NewMaxDepth = pp_constraints(List, NewSeparator, Level + 1, MaxDepth, State),
%  io:format(")", []),
%  NewMaxDepth;
%pp_constraints([#constraint_list{type = Type, list = List, id = Id}|Tail],
%	       Separator, Level, MaxDepth, State) ->
%  io:format("List ~w(", [Id]),
%  NewSeparator = case Type of
%		   conj -> "*";
%		   disj -> "+"
%		 end,
%  NewMaxDepth = pp_constraints(List, NewSeparator, Level+1, MaxDepth, State),
%  io:format(") ~s\n~s ", [Separator, Separator]),
%  pp_constraints(Tail, Separator, Level, NewMaxDepth, State).
%-else.
%pp_constrs_scc(_SCC, _State) ->
%  ok.
%-endif.

-ifdef(TO_DOT).

constraints_to_dot_scc(SCC, State) ->
  io:format("SCC: ~p\n", [SCC]),
  Name = lists:flatten([io_lib:format("'~w'", [debug_lookup_name(Fun)])
			|| Fun <- SCC]),
  Cs = [state__get_cs(Fun, State) || Fun <- SCC],
  constraints_to_dot(Cs, Name, State).

constraints_to_dot(Cs0, Name, State) ->
  NofCs = length(Cs0),
  Cs = lists:zip(lists:seq(1, NofCs), Cs0),
  {Graph, Opts, _N} = constraints_to_nodes(Cs, NofCs + 1, 1, [], [], State),
  hipe_dot:translate_list(Graph, "/tmp/cs.dot", "foo", Opts),
  Res = os:cmd("dot -o /tmp/"++ Name ++ ".ps -T ps /tmp/cs.dot"),
  io:format("Res: ~p~n", [Res]),
  ok.

constraints_to_nodes([{Name, #constraint_list{type = Type, list = List, id=Id}}
		      |Left], N, Level, Graph, Opts, State) ->
  N1 = N + length(List),
  NewList = lists:zip(lists:seq(N, N1 - 1), List),
  Names = [SubName || {SubName, _C} <- NewList],
  Edges = [{Name, SubName} || SubName <- Names],
  ThisNode = [{Name, Opt} || Opt <- [{label,
				      lists:flatten(io_lib:format("~w", [Id]))},
				     {shape, get_shape(Type)},
				     {level, Level}]],
  {NewGraph, NewOpts, N2} = constraints_to_nodes(NewList, N1, Level+1,
						 [Edges|Graph],
						 [ThisNode|Opts], State),
  constraints_to_nodes(Left, N2, Level, NewGraph, NewOpts, State);
constraints_to_nodes([{Name, #constraint{lhs = Lhs, op = Op, rhs = Rhs}}|Left],
		     N, Level, Graph, Opts, State) ->
  Label = lists:flatten(io_lib:format("~s ~w ~s",
				      [format_type(Lhs), Op,
				       format_type(Rhs)])),
  ThisNode = [{Name, Opt} || Opt <- [{label, Label}, {level, Level}]],
  NewOpts = [ThisNode|Opts],
  constraints_to_nodes(Left, N, Level, Graph, NewOpts, State);
constraints_to_nodes([{Name, #constraint_ref{id = Id0}}|Left],
		     N, Level, Graph, Opts, State) ->
  Id = debug_lookup_name(Id0),
  CList = state__get_cs(Id0, State),
  ThisNode = [{Name, Opt} || Opt <- [{label,
				      lists:flatten(io_lib:format("~w", [Id]))},
				     {shape, ellipse},
				     {level, Level}]],
  NewList = [{N, CList}],
  {NewGraph, NewOpts, N1} = constraints_to_nodes(NewList, N + 1, Level + 1,
						 [{Name, N}|Graph],
						 [ThisNode|Opts], State),
  constraints_to_nodes(Left, N1, Level, NewGraph, NewOpts, State);
constraints_to_nodes([], N, _Level, Graph, Opts, _State) ->
  {lists:flatten(Graph), lists:flatten(Opts), N}.

get_shape(conj) -> box;
get_shape(disj) -> diamond.

-else.
constraints_to_dot_scc(_SCC, _State) ->
  ok.
-endif.

-module(get_core).

-compile(export_all).


main()->
	{ok,Core}=dialyzer_utils:get_core_from_src("temp.erl", [no_copt]),
%	{ok,_,AbstrCode} = compile:file("temp.erl", [to_pp, binary, no_copt ]),
%	io:format("AbstrCode: ~p\n",[AbstrCode]),
%	{ok, _, Core} = compile:forms(AbstrCode, [no_copt, to_core, binary, return_errors,
%   					no_inline, strict_record_tests, strict_record_updates,
%   					no_is_record_optimization]),
%	io:format("CORE: ~p\n",[Core]),
	{LabeledCore_,_} = cerl_trees_:label(Core,0),
	{LabeledCore,_} = cerl_trees:label(LabeledCore_,0),
	{ok, DeviceCore} = file:open("temp.core_slice", [write]),
	io:format(DeviceCore, "~p", [LabeledCore]),
	ok = file:close(DeviceCore),
	{OriLabeledCore,_} = cerl_trees:label(Core,0),
	{ok, DeviceCoreOri} = file:open("temp.core_original", [write]),
	io:format(DeviceCoreOri, "~p", [OriLabeledCore]),
	ok = file:close(DeviceCoreOri).
	
cleanup_parse_transforms([{attribute, _, compile, {parse_transform, _}}|Left]) ->
  cleanup_parse_transforms(Left);
cleanup_parse_transforms([Other|Left]) ->
  [Other|cleanup_parse_transforms(Left)];
cleanup_parse_transforms([]) ->
  [].
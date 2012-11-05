-module(ex10).
-export([main/1]).

main(X) ->
  case X of
    3 ->
      case X of
        2 -> 0
      end
  end.

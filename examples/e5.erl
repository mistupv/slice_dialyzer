-module(e5).

-export([main/1]).

main(X)->
        Y = f(X),
	case Y of
	     Z when is_tuple(Z) -> ok
	end.
	
	
f(0) -> 1.
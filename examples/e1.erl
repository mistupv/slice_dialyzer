-module(e1).

-export([main/1]).

main(X)->
	case X of
	     1 -> a;
	     3 -> c
	end,
	f(X).

f(2) -> a.
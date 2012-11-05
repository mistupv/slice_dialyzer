-module(e7).

-export([main/1]).

main(X)->
	f(X),
	g(X),
	h(X).
	
	
f(X) -> i(X).

i(1)->a;
i(2)->b;
i(3)->	case 0 of
	     1 -> c
	end.

g(1)->a;
g(4)->b.

h(4)->c.
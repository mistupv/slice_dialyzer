-module(e2).

-export([main/1]).

main(X)->
	f(X),
	g(X),
	h(X).
	
	
f(X) -> i(X).

i(1)->a;
i(2)->b;
i(X)->case X of 
           3 -> c
      end.

g(1)->a;
g(4)->b.

h(4)->c.
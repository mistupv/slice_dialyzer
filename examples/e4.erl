-module(e5).

-export([main/1]).

main(X)->
	A=f(X),
	Y=g(X,a),
	Z=f(Y),
	case Z of
	     0 -> g(A,X)
	end.
	
f(0)->0;
f(1)->1.

g(1,a)->0.
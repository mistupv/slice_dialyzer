-module(e8).

-export([main/1]).

main(X) -> 
	Y = f(X),
	[Y|X].
	
f(a) -> a.

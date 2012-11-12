-module(e9).

-export([main/1]).

main(X) -> 
	Z = case X of
	     a -> 1;
	     b -> 2
	    end,
	case Z of
  	     1 -> a;
  	     3 -> c;
  	     2 -> b;
	     _ -> Z
           end.

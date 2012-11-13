-module(e10).

-export([main/1]).

main(X) ->
   case X of
        2 -> 
          case X of
               1 -> a;
               2 -> b;
               Y -> Y
          end
   end.
-module(e10).

-export([main/1]).

main(X) ->
   case X of
        1 -> 
          case X of
               2 -> a;
               Y -> Y;
               _ -> b
          end
   end.
-module(temp).

-export([main/1]).

main(X) -> 
%{X,X}.
        %F=fun(Z) -> Z+1 end,
        %g(X),
%	h(X).
	%[F(X_)||X_<-[1,2,3],X==X_].
	%[F(X_)||X_<-[1,2,3]].
	%[X_||X_<-[1,2]].
	

%g(1)->1;
%g(2)->2;
%g(3)->3;
%g(4)->4.	

%	f(X+1),
	%g(X),
	%h(X+1),
	%i(X).
%	case X of 
%	     1 -> 1;
%	     2 -> 2
%	end,
%	case X of
%	     3 -> 3
%	end.

	
%	case X of
%	     a -> a;
%	     b -> b
%	end,
%	case X of
%	     a -> a
%	end,
	
%	F(X).
%	case X of
%	     c -> c
%	end.
%	g(X),
	%F(X).
%	case X of
%	     1 -> 1;
%	     a -> 2
%	end,
%        case X of
%	     2 -> 1
%	end.

%f(X)->X.
%
%
%h(X) -> X=3.
%
%i(1)->1;
%i(3)->3.
	
%f(a)-> a.

%g(a)->a;
%g(b)->b.
%
%h(c)->c.



%%%%%%%PETA

%	case X of
%	     1 -> a;
%	     2 -> b;
%	     3 -> c
%	end,
%	case X of
%	     1 -> a;
%	     3 -> c
%	end,
%	f(X).
%
%f(2) -> a.


%NO SACA LO DE LA f

%	f(X),
%	g(X),
%	h(X).
%	
%	
%f(1)->1;
%f(2)->1;
%f(3)->1.
%
%g(1)->1;
%g(3)->1.
%
%h(2)->2.

	f(X),
	g(X),
	h(X)+i(X).
	
	
f(1)->a;
f(2)->b;
f(3)->c.

i(X)->		
        case X of
	     1 -> case X of
	               2 -> a
	          end
	end.

g(1)->a;
g(2)->c;
g(4)->b.

h(4)->0.

%	Y=f(X),
%	case {X,Y} of
%	     {1,2} -> a;
%	     {1,2,3} -> b;
%	     {1,3} -> c
%	end,
%	g(X).
%	
%f(1) -> 3.
%g(2) -> a.
-module(temp).


%-export(export_all).

%c(temp,[no_copt, to_core, return_errors,no_inline, strict_record_tests, strict_record_updates,no_is_record_optimization]). 

%main()->
%	X=[],
%	Y=42,
%	case X of
%		 [] -> [];
%		 0  -> Y
%	end.

%main(N) when is_number(N)->t(N).
%
%t(N) when is_integer(N) ->
%	X = f(3.14) + N,
%	n(42) + n(X);	
%t(N) when is_atom(N)->
%	f(N).
%	
%f(N) -> N + 2.
%
%n(N) -> N + 1.

%main()->
%	X={3,1},
%	Y={X,3},
%	Y={X,3}.

%main(X)-> case X of
%			   0 ->1;
%			   X->f(3)
%		  end,
%		  Y=f(X),
%		  case Y of
%		  	   0->0;
%		  	   4->4;
%		  	   1->1;
%		  	   1->1;
%		  	   2->2;
%		  	   0->0
%		  end,
%		  Y= case X of
%		  		  0->0;
%		  		  1->1;
%		  		  2->2;
%		  		  3->3;
%		  		  _->5
%		     end,
%		  f(Y).


%-compile(export_all).

%main(X)->
%
%%		  f(X),
%%		  g(X),
%%		  h(X).
%%		  1(3).
%		  Y=X+1,
%		  case Y of
%		       0->1
%		  end(3).

%f(0) -> 0;
%f(1) -> 1;
%f(2) -> 2. 
%
%g(0) -> 0;
%g(1) -> 1. 
%
%h(0) -> 0;
%h(1) -> 1;
%h(2) -> 2.





%	  Y=X,
%	  case X of
%	       0->1;
%	       1->2;
%	       2->Y
%	  end,
%	  Z=Y*3,
%	  case X of
%	       3->Z
%    	  end.


%	case X of
%		0 -> 0;
%		1 -> 1;
%		3 -> 3
%	end,
%	case X of
%		0 -> 0;
%		1 -> 1;
%		2 -> 2
%	end,
%	case X of
%		2 -> 2
%	end.



%        Y=X+1,
%	case Y of
%	     0->1
%	end(3).

%	Z=b,
%	Y=5,
%	X=a,
%	A=Y+Z,
%	A+X.
	
	





%	X+3,
%	f(X,X),
%	g(X).
%	
%f(0,0)->2;
%f(1,1)->3.
%
%g(a)->b.





%	g(f(X)).
%	
%f(1)->1;
%f(2)->2;
%f(3)->3.
%
%g(a)->a.
% 
	  



%	  
%	  Y=X, 
%	  case X of
%	       1 -> 1;
%	       2 -> 2
%	  end,
%	  case Y of 
%	       2 -> 2;
%	       3 -> 3
%          end,   
%          X=1.	
%	


%HISTORIAL
%	case X of
%		0 -> 0;
%		1 -> 1;
%		3 -> 3
%	end,
%	case X of
%		0 -> 0;
%		1 -> 1;
%		2 -> 2
%	end,
%	case X of
%		2 -> 2
%	end.


%NO VAN

%	F = fun(3)->0 end,
%	F(2).


%	(fun (3,0) -> 1 end)(2,0).

%	Y= (fun (3) -> X;(2)->0 end)(2),
%	1=Y.

%	(fun (2)->2 end)(X),


	  %Y=X+1,
%	  case X of
%	       0->1
%	  end(3).

%	  Y=X+1,
%	  case Y of
%	       0->1
%	  end,
%	  Y(3).

%	  Y=X+1,
%	  case X of
%	       0->1
%	  end,
%	  Y(3).

%	f(X),
%	2=X,
%	h(X).  
%
%
%
%f(X) -> g(X).
%
%g(0) -> 0;
%g(1) -> 1;
%g(2) -> 2.  
%
%h(0) -> 0.

%
%	Y=X+5,
%	X=a.
	
	
%	case X of
%		0 -> 0;
%		1 -> 1;
%		2 -> 2
%	end,
%	case X of
%		0 -> 0;
%		1 -> 1
%	end,
%	case X of
%		0 -> 0
%	end,
%	case X of
%		2 -> 2
%	end.



-export([main/1]).

main(X) ->
	%F=fun(Y) -> X+Y end,
	F=fun(Z) -> Z+1 end,
	%Z=X+1,
	f(X),
	F(X).
	
f(a)-> a.
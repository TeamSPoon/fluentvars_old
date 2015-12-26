Attributed Prolog variables that may remain (Free) attributed prolog variables even after unifying with nonvars! 

This can work out fine when the programmer is thinking the goal was to deal with foreign (non prolog datatypes) such as xpce refs,  or pattern matchers,   .. The attributed variable does a "check" durring unification and "it decides" (using hooks) the ways in which it will be manipulated by the unification.

Sound bizare?

Not so much, currently this is true:  

````
?-  freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant).
Foo = break_me(cant).
````

This new peice of code shows simular abnormality 

````
%% subsumer_var(-X) is det.
%
%  Each time it is bound, it potentially becomes less bound!
%
%
% subsumer_var(X):- termsource(X),init_accumulate(X,subsumer_var,term_subsumer).
%
% ==
%  ?-  subsumer_var(X), X= a(1), X = a(2).
%  X = a(_)  ;
% false.
%
%  ?-  subsumer_var(X), X= a(1), X = a(2),  X=a(Y).
% X = a(Y).
% Y = _G06689  ;
% false.
%
%  ?-  subsumer_var(X), X= a(1), X = a(2),  X=b(1).
% false
% ==
%

subsumer_var(X):- mvar_set(X,+remainVar),init_accumulate(X,pattern,term_subsumer).

init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).

accume:verify_attributes(Var,Value,[]):- get_attr(Var,accume,Attr),accum_hook(Attr,Value).

% we have our first value!
accum_hook(init_accumulate(Var,M,P),Value):- nonvar(Value),!,put_attr(Var,accume,accume_value(Var,M,P,Value)).
% some other attribute module is trolling us (make no internal changes)
accum_hook(init_accumulate(_,_,_),Value):- !,var(Value).
% we have our subsumer job 
accum_hook(accume_value(Var,M,P,Prev),Value):- nonvar(Value),!,call(P, Prev,Value,Combined),nonvar(Combined),put_attr(Var,accume,accume_value(Var,M,P,Combined)).
% Someone passed a variable and we are a "termsource" (this is the signal to drain the bilge)
accum_hook(accume_value(_Var,_M,P,Prev),Value):-  var(Value),!, nonvar(P), wno_hooks(Prev=Value).
````


And it is even OK to have variables that are (in themselves)  able to turn unification with '='/2 into a choice point factory.
````
?- when(nonvar(X),member(X,[a(1),a(2),a(3)])), !, X=a(_).
X = a(1) ;
X = a(2) ;
X = a(3).
````

This library will explore examples of such possible chicanery as well as very usefully tricks that are available with TermSinks.



Hopefully this note does not distract too much... 

When implementing the C support for Paul Tarau's  (TermsSink/TermSource) Fluents  I had scenarios I replaced one end of unify with a copy_term of the Var .. and then  ran wakeup/1 on that Copy thus leaving the original Var free to move on.   I know that sounds almost obscene and unsupportable .. However  it worked out just fine and as long as I was thinking the goal was to deal with foreign (non prolog datatypes) such as xpce refs,  or pattern matchers,   .. the attributed variable is willing to do a "check" on anything it unifies to letting "it decide" the ways in which it was to be manipulated.  It may internally change its resulting value and even change the other sides values (not forced into the other side's of unifications expectations)

For example, we want the below to be true:

````
?-  freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant).
Foo = break_me(cant).
````

This is a different piece of code but it shows the same heresy! 

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


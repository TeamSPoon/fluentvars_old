:- module(demo, [ demo/1]).
demo(Var) :- put_attr(Var, demo, x).
verify_attributes(Var, _Value, [hello(Var)]).
hello(Var) :- writeln(Var).
attr_unify_hook(_,_).

/*

demo(X), X = 1.
Wakeup: wakeup(system,_G1500,att(demo,x,[]),1,[])
1
X = 1
So far, so good. But ... we only get one wakeup here.

demo(X), a(X,Y) = a(1,2).
Wakeup: wakeup(system,_G1584,att(demo,x,[]),1,[])
1
X = 1,
Y = 2.
Or this. I think this should fail right away, no? Now we get dif(X,a), a(X,X) = a(1,2) succeeds with X=1. I fear that the verification hook gets really complicated if unification does not already catch this.

demo(X), a(X,X) = a(1,2).
Wakeup: wakeup(system,_G1572,att(demo,x,[]),1,wakeup(system,_G1572,att(demo,x,[]),2,[]))
1
X = 1.

*/

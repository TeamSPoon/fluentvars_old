:- use_module(library(clpb)).
:- ensure_loaded(shower).

sat(_)  --> [].
sat(X*Y) --> [_], sat(X), sat(Y).
sat(X+Y) --> [_], sat(X), sat(Y).
sat(X#Y) --> [_], sat(X), sat(Y).

vs_eqs(Vs, Eqs) :- phrase(vs_eqs(Vs), Eqs).

vs_eqs([]) --> [].
vs_eqs([V|Vs]) --> vs_eqs_(Vs, V), vs_eqs(Vs).

vs_eqs_([], _) --> [].
vs_eqs_([V|Vs], X) --> vs_eqs_(Vs, X), ( [X=V] ; [] ).

run :-
        length(Ls, N),
        portray_clause(N),
        phrase(sat(Sat), Ls),
        term_variables(Sat, Vs0),
        permutation(Vs0, Vs),
        vs_eqs(Vs, Eqs),
        findall(Vs, (sat(Sat),maplist(call, Eqs),labeling(Vs)), Sols1),
        findall(Vs, (labeling(Vs),maplist(call,Eqs),sat(Sat)), Sols2),
        (   sort(Sols1, Sols), sort(Sols2, Sols) -> true
        ;   throw(neq-Sat-Eqs-Vs0-Vs-Sols1-Sols2)
        ),
        false.


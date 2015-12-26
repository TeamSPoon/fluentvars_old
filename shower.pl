:- use_module(library(clpfd)).
:- use_module(library(logicmoo_utils)).
:- [clpb_test].

shower(S, Done) :-
        D = [5, 3, 8, 2, 7, 3, 9, 3],
        R = [1, 1, 1, 1, 1, 1, 1, 1],
        length(D, N),
        length(S, N),
        S ins 0..100,
        Done in 0..100,
        maplist(ready(Done), S, D),
        tasks(S, D, R, 1, Tasks),
        cumulative(Tasks, [limit(3)]),
        labeling([], [Done|S]).


tasks([], _, _, _, []).
tasks([S|Ss], [D|Ds], [R|Rs], ID0, [task(S,D,_,R,ID0)|Ts]) :-
        ID1 #= ID0 + 1,
        tasks(Ss, Ds, Rs, ID1, Ts).

ready(Done, Start, Duration) :- Done #>= Start+Duration.



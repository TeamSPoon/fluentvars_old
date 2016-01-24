:- use_module(library(clpfd)).
:- use_module(library(lists)).

sat(X) :- X in 0..9.

num(L) :-
    solve(As,Bs,Cs,Ds),
    append([As,Bs,Cs,Ds], Vs),
    findall(., labeling([ff], Vs), Ls),
    length(Ls, L).

solve([A1,A2,A3,A4],[B1,B2,B3,B4],[C1,C2,C3,C4],[D1,D2,D3,D4]) :-
    maplist(sat, [A1,A2,A3,A4,B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4]),
    A1 + A2 + A3 + A4 #= B1 + B2 + B3 + B4,
    A1 + A2 + A3 + A4 #= C1 + C2 + C3 + C4,
    A1 + A2 + A3 + A4 #= D1 + D2 + D3 + D4,
    A1 + A2 + A3 + A4 #= A1 + B1 + C1 + D1,
    A1 + B1 + C1 + D1 #= A2 + B2 + C2 + D2,
    A1 + B1 + C1 + D1 #= A3 + B3 + C3 + D3,
    A1 + B1 + C1 + D1 #= A4 + B4 + C4 + D4,
    A1 + A2 + A3 + A4 #= A1 + B2 + C3 + D4,
    A1 + B2 + C3 + D4 #= A4 + B3 + C2 + D1.

mytime(G):- statistics(runtime, [T0|_]),
        G,
        statistics(runtime, [T1|_]),
        T is T1 - T0,
        format('~q took ~3d sec.~n', [G,T]).

:- mytime(num(_X)).

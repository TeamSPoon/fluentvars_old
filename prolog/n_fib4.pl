:- use_module(library(clpfd)).

n_fib4(0, 1).
n_fib4(1, 1).
n_fib4(N, F) :-
    N #> 1, N1 #= N - 1, N2 #= N - 2,
    n_fib4(N1, F1), n_fib4(N2, F2),
    false.

% :- time(n_fib4(N, 3)).

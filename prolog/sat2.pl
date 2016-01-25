
%va3=verify_attributes/3,
%emu=emulate attr_unify_hook/2
%auh2=attr_unify_hook/2
:- current_prolog_flag(argv,[W]),set_prolog_flag(clp,W).
:- current_prolog_flag(dialect,sicstus) 
   -> 
    (use_module(library(lists)),
     use_module(library(between))) 
    ; true.

mytime(G):- 
   current_prolog_flag(dialect,sicstus)
   ->  mytime0(G);time(mytime0(G)).

mytime0(G):- statistics(runtime, [T0|_]),
        G,!,
        statistics(runtime, [T1|_]),
        T is T1 - T0,
        format('~q took ~3d sec.~n', [G,T]).


:- use_module(library(clpfd)).

sat(N,X) :- X in 0..N.

num(L):- between(3,6,N),time(num(N,L)),writeln(num(N=L)),fail.
num(N,L) :-
    solve(N,As,Bs,Cs,Ds),
    append([As,Bs,Cs,Ds], Vs),
    findall(., labeling([ff], Vs), Ls),
    length(Ls, L).

solve(N,[A1,A2,A3,A4],[B1,B2,B3,B4],[C1,C2,C3,C4],[D1,D2,D3,D4]) :-
    maplist(sat(N), [A1,A2,A3,A4,B1,B2,B3,B4,C1,C2,C3,C4,D1,D2,D3,D4]),
    A1 #=< D4,
    A1 #=< D1,
    A1 + A2 + A3 + A4 #= B1 + B2 + B3 + B4,
    A1 + A2 + A3 + A4 #= C1 + C2 + C3 + C4,
    A1 + A2 + A3 + A4 #= D1 + D2 + D3 + D4,
    A1 + A2 + A3 + A4 #= A1 + B1 + C1 + D1,
    A1 + B1 + C1 + D1 #= A2 + B2 + C2 + D2,
    A1 + B1 + C1 + D1 #= A3 + B3 + C3 + D3,
    A1 + B1 + C1 + D1 #= A4 + B4 + C4 + D4,
    A1 + A2 + A3 + A4 #= A1 + B2 + C3 + D4,
    A1 + B2 + C3 + D4 #= A4 + B3 + C2 + D1.


end_of_file.

?- time(num(4,_)).



% :- mytime(num(_)).




DM: replaced commas in text as to not confuse results to someone reading this file

========================================================================
SICStus 4.3.2 (x86_64-linux-glibc2.12)

#sicstus -l sat2.pl
num(3=2492) took 0.060 sec.
num(4=13240) took 0.250 sec.
num(5=52400) took 1.130 sec.
num(6=171220) took 4.000 sec.



========================================================================
SWI  Version 7.3.15-29-g6a6915a-DIRTY 

#swipl15 -O -l sat2.pl va3
num(3=2492) took 3.902 sec. % 22,168,440 inferences, 3.942 CPU in 3.944 seconds (100% CPU, 5624249 Lips)
num(4=13240) took 22.779 sec.  % 128,174,772 inferences, 23.088 CPU in 23.103 seconds (100% CPU, 5551555 Lips)
num(5=52400) took 99.521 sec. % 555,719,358 inferences, 99.522 CPU in 99.587 seconds (100% CPU, 5583897 Lips)
num(6,171221) (+1?!) took 353.829 sec. % 1,971,478,876 inferences, 353.830 CPU in 354.076 seconds (100% CPU, 5571832 Lips)




========================================================================
SWI 7.3.15-31-g2988c00-DIRTY  Fluents/TermSinks ( -O2 )

#swipl -O -l sat2.pl auh2
/* call old AUH2 */
num(3=5400) took 6.212 sec. % 49,544,580 inferences, 6.214 CPU in 6.216 seconds (100% CPU, 7973312 Lips)
num(4=30277) took 37.731 sec. % 303,152,413 inferences, 37.748 CPU in 37.759 seconds (100% CPU, 8030968 Lips)
num(5=125794)  took 172.602 sec. % 1,361,278,436 inferences, 172.602 CPU in 172.746 seconds (100% CPU, 7886802 Lips)
num(6=423097) took 626.945 sec. % 4,915,103,733 inferences, 626.945 CPU in 627.587 seconds (100% CPU, 7839763 Lips)

#swipl -O -l sat2.pl emu
/* calls old AUH2 from VA3 */
num(3=5403) (+3) took 6.305 sec. % 49,618,214 inferences, 6.307 CPU in 6.313 seconds (100% CPU, 7867227 Lips)
num(4=30286) (+11) took 38.726 sec. % 303,339,445 inferences, 38.743 CPU in 38.783 seconds (100% CPU, 7829585 Lips)
num(5=125811) (+17) took 175.605 sec. % 1,361,215,617 inferences, 175.605 CPU in 175.792 seconds (100% CPU, 7751565 Lips)
num(6=423125) (+28) took 637.541 sec. % 4,912,372,862 inferences, 637.541 CPU in 638.213 seconds (100% CPU, 7705185 Lips)

#swipl -O -l sat2.pl va3
/* calls new VA3 */
num(3=5400) took 6.606 sec. % 50,207,726 inferences, 6.607 CPU in 6.609 seconds (100% CPU, 7598643 Lips)
num(4=30277) took 41.074 sec. % 311,501,837 inferences, 41.085 CPU in 41.099 seconds (100% CPU, 7581842 Lips)
num(5=125796) (+2) took 185.450 sec. % 1,411,331,686 inferences, 185.450 CPU in 185.599 seconds (100% CPU, 7610306 Lips)
num(6=423130) (+33) took 675.805 sec. % 5,124,383,039 inferences, 675.805 CPU in 676.334 seconds (100% CPU, 7582634 Lips)



========================================================================
% SWI 7.2.3 num(3=5400) took 5.035 sec.
% SWI 7.3.15 num(3=5400) took 6.282 sec.
% SWI 7.3.15-31-g2988c00-DIRTY num(3=5400) took 6.285 sec.
% Yap 6.2.2 num(3=5400) took 3.522 sec.
% SICStus 4.3.2 (x86_64-linux-glibc2.12) -> num(3=5400) took 0.120 sec.




/*  Part of SWI-Prolog

    Author:        Douglas R. Miles
    E-mail:        logicmoo@gmail.com 
    WWW:           http://www.swi-prolog.org http://www.prologmoo.com
    Copyright (C): 2015, University of Amsterdam
                                    VU University Amsterdam


    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(fluent_vars,[
      wno_fluents/1,w_fluents/1,
      w_fbs/2,
        wno_dmvars/1,w_dmvars/1,
  wno_debug/1,w_debug/1,
          fluent_default/0,
          testfv/0, 
          % TODO remove  above before master
      fluent_override/2,
      fluent_overriding/2,
      '$fluent_default'/2,
      fluent_default/2,
      fluent_default/1,
      new_fluent/2,
      sink_fluent/1,
      fluent/1,
      source_fluent/1,
      dc_fluent/1,
      merge_fbs/3,
      any_to_fbs/2,
      fbs_to_number/2]).


% TODO END remove before master
:- meta_predicate must_tst_det(0).
:- meta_predicate must_tst(0).
:- meta_predicate mcc(0,0).
% TODO END remove before master

:- meta_predicate wno_fluents(+).
:- meta_predicate wno_dmvars(+).
:- meta_predicate wno_debug(+).
:- meta_predicate w_fluents(+).
:- meta_predicate w_fbs(+,+).
:- meta_predicate w_dmvars(+).
:- meta_predicate w_debug(+).
:- module_transparent((
  wno_fluents/1,w_fluents/1,w_fbs/2,
  wno_dmvars/1,w_dmvars/1,
  wno_debug/1,w_debug/1)).
 

:- nodebug(fluents).

:- multifile(user:fluent_hook/4).
:- dynamic(user:fluent_hook/4).
user:fluent_hook(Pred,Var,Value,RetCode):-dmsg(user:fluent_hook(Pred,Var,Value,RetCode)),fail.


% TODO BEGIN remove before master

:- [swi(boot/attvar)].
:- redefine_system_predicate('$attvar': collect_va_goal_list/5).
:- abolish('$attvar': collect_va_goal_list/5).
% Disables extended Fluent/Attvar wakeups and hooks durring processing.
'$attvar':collect_va_goal_list(A,B,C,D,E):- wno_fluents(fixed_collect_va_goal_list(A,B,C,D,E)).

fixed_collect_va_goal_list(_, Var , Value) --> {\+ attvar(Var),!,Var=Value}.
fixed_collect_va_goal_list(att(Module, AttVal, Rest), Var, Value) --> !,
        {dmsg(att(Module, AttVal, Rest))},
        { wo_fluent(Var,w_fluents(Module:verify_attributes(Var, Value, Goals))) },
        '$attvar':goals_with_module(Goals, Module),
        fixed_collect_va_goal_list(Rest, Var, Value).
fixed_collect_va_goal_list([],_,_) --> !.
fixed_collect_va_goal_list(Pred,Var,Value) --> 
    {wo_fluent(Var,w_fluents(user:fluent_hook(Pred,Var,Value,List)))*->true;List=[]},
    List.

% TODO END remove before master


'$fluent_default'(G,S):-'$fluent_default'(G,S,I,I).

%%	sink_fluent(-Fluent) is det.
%
% Base class of "SinkFluent" that recieves bindings

sink_fluent(Fluent):-fluent_override(Fluent,+sink_fluent).


%%	source_fluent(-Fluent) is det.
%
% Base class of "SourceFluent" that creates bindings

source_fluent(Fluent):-fluent_override(Fluent,+source_fluent).


%%	dc_fluent(-Fluent) is det.
%
% Create a truely don't care '_' Fluent
% Will unify multiple times and remain a var
% even after binding. At bind with anything and call no wakeups
% peer or otherwise
% Tarau's "EmptySink" fluent

dc_fluent(Fluent):-fluent_override(Fluent,no_wakeup+no_bind-peer_wakeup+no_disable).


%%	fluent_default(+Get,+Set) is det.
%
% Get/Set system wide fluent modes
% Examples:
%
% ==
% ?- fluent_default(_,+disable). % Disable entire system
% ==

fluent_default(Get,Set):- '$fluent_default'(Get,Get),merge_fbs(Set,Get,XM),must_tst('$fluent_default'(_,XM)).


%% fluent_default(+Set) is det.
%
% Set system wide fluent modes
%
% == 
% ?-listing(bits_for_fluent_default/1) to see them.
% ==

fluent_default(X):-number(X),!,'$fluent_default'(_,X),fluent_default.
fluent_default(X):- var(X),!,'$fluent_default'(X,X).
fluent_default(X):- '$fluent_default'(M,M),merge_fbs(X,M,XM),must_tst('$fluent_default'(_,XM)),!,fluent_default,!.


bits_for_fluent_default(v(

/* '$fbs' = 18 FluentBitS: these bits in an prolog accessable  get_attr/3,putt_attr/3 need it fit in valInt()*/
  no_bind              = 0x0001, "C should let wakeup/1 do binding",
  no_wakeup            = 0x0002, "C should skip scheduling a $wakeup/1 ",
  mid_unify            = 0x0004, "do_unify() has called unify",
  peer_wakeup          = 0x0008, "attempt to schedule a wakeup on other attvar peers we unify with",
  peer_trail           = 0x0010, "Those scheduled peers should trail assignment",
  on_unify_keep_vars   = 0x0020, "whenever unifying with a plain variable send the variable to $wakeup/1 as the value",
  unify                = 0x0020, "SAME AS ABOVE used in do_unify()",
  on_unify_replace     = 0x0040, "UNUSED unify replace",
  no_trail             = 0x0080, "Do not bother to trail the previous value",

/* schedule wakeup and can_unify for remote remote terms */
  colon_eq         = 0x0100, "override(unify_vp) like on_unify_keep_vars except happens in unify_vp()",
  bind             = 0x0200, "override(bind_const) like on_unify_keep_vars except happens in bindConst()",
  strict_equal     = 0x0400, "Allows Fluents to implement their own structurally equivalence",
  at_equals        = 0x0800, "Allows Fluents to implement their own variant-ness",
  no_inherit     =  0x1000, "This Fluent doest not inherit from fluent_default flags (otherwise they are or-ed)",
  copy_term      =  0x2000, "UNUSED override(copy_term) would allow Fluents to implement their own copy.. (for constants like EmptySinkFluents)",
  compare        =  0x4000, "UNUSED override(compare) would allow Fluents to decide their non-standard ordering against each other",
  disabled       =  0x8000, "Treat this Fluent as a plain attributed variable (allow the system to operate recusively.. implies no_inherit) ",
  check_vmi      = 0x010000, "LD->slow_unify might need tp be true for us to work (mostly for testing)",
  vmi_ok         = 0x030000, "LD->slow_unify is/was not needed",
  save_wakeup    = 0x040000, "saveWakeup before scheduling",
  immediate      = 0x080000, "run foreignWakeup immediatly after schedule",
  spy            = 0x100000, "spy on fluent",
  debug          = 0x100000, "spy on fluent",


         % Aliases
         override(=)  = override(unify),
          variant = at_equals,
         unify_vp = colon_eq,
         override(==)  = override(strict_equal),
         override(=@=)  = override(variant),
         override(\=)  = override(unify),
         override(\=@=)  = override(variant),
         override(\==)  = override(strict_equal),

         eagerly =(+override(bind)+override(unify_vp)+override(unify)+on_unify_keep_vars),
         comparison =(+override(compare)+override(variant)+override(strict_equal)+override(unify)),
         override_all = (+eagerly+comparison+override(copy_term)+peer_wakeup),
         [] = 0,
         sink_fluent=(+no_bind+peer_wakeup+eagerly), % no_inherit+
         source_fluent=(+no_bind+peer_wakeup+override(unify)+on_unify_keep_vars+override(bind))
    )). 

%% fluent_default is det.
%
% Print the system global modes
%
fluent_default:-'$fluent_default'(M,M),any_to_fbs(M,B),format('~N~q.~n',[fluent_default(M=B)]).


%% debug_fluents is det.
%
% Turn on extreme debugging
%
debug_fluents(true):-!, fluent_default(+debug_fluents+debug_extreme).
debug_fluents(_):- fluent_default(-debug_fluents-debug_extreme).

%%    fluent_overriding(Fluent,BitsOut)
%
% Get fluent properties
%

fluent_overriding(Fluent,BitsOut):- wno_fluents(get_attr(Fluent,'$fbs',Modes)->any_to_fbs(Modes,BitsOut);BitsOut=0).


%%    fluent_override(Fluent,BitsOut)
%
% Set fluent properties
%

fluent_override(Fluent,Modes):-
 wno_fluents((var(Fluent),
  ((
   get_attr(Fluent,'$fbs',Was)->
       (merge_fbs(Modes,Was,Change),put_attr(Fluent,'$fbs',Change)); 
   (fbs_to_number(Modes,Number),put_attr(Fluent,'$fbs',Number)))))),!.


%%    fluent(+Fluent)
%
% Checks to see if a term is a fluent

fluent(Fluent):-wno_fluents(get_attr(Fluent,'$fbs',_)).

%%    new_fluent(+Bits,-Fluent) is det.
%
% Create new fluent with a given set of Properties

new_fluent(Bits,Fluent):-fluent_override(Fluent,Bits).

%%    set_persistent(+Fluent,+YesNo)
%
% Dynamically sets the persistence status of this Fluent. A persistent Fluent will not have its 
% stop undo automatically called upon backtracking.  A typical example would be a file or socket 
% handle to be reused after backtracking.  This is simular to what might happen if every unification 
% used nb_setval(MyFluent,SomeValue) instead of b_setval/2 except in this case MyFluent
% is a prolog variable instead of an atom.

set_persistent(Var,YesNo):- 
  YesNo=yes ->  
    attvar_override(Var,+no_trail) ; 
    attvar_override(Var,-no_trail) .

:- '$fbs':export('$fbs':verify_attributes/3).
:-     export('$fbs':verify_attributes/3).

        '$fbs':verify_attributes(_,_,[]).
verify_attributes(_,_,[]).
contains_fbs(Fluent,Bit):- any_to_fbs(Fluent,Bits),!,member(Bit,Bits).

any_to_fbs(BitsIn,BitsOut):-  
 fbs_to_number(BitsIn,Mode),
   Bits=[Mode],bits_for_fluent_default(MASKS),
   ignore((arg(_,MASKS,(N=V)),nonvar(V),fbs_to_number(V,VV), VV is VV /\ Mode , fluent_vars:nb_extend_list(Bits,N),fail)),!,
   BitsOut = Bits.


nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).

must_tst(G):- G*-> true; throw(must_tst_fail(G)).

must_tst_det(G):- G,deterministic(Y),(Y==true->true;throw(must_tst_fail(G))).


merge_fbs(V,VV,VVV):-number(V),catch((V < 0),_,fail),!, V0 is - V, merge_fbs(-(V0),VV,VVV),!.
merge_fbs(V,VV,VVV):-number(V),number(VV),VVV is (V \/ VV).
merge_fbs(V,VV,VVV):-var(V),!,V=VV,V=VVV.
merge_fbs(set(V),_,VVV):-fbs_to_number(V,VVV),!.
merge_fbs(V,VV,VVV):-var(VV),!, fbs_to_number(V,VVV),!.
merge_fbs(+(A),B,VVV):- must_tst((fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V \/ VV))).
merge_fbs(*(A),B,VVV):- fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V /\ VV).
merge_fbs(-(B),A,VVV):- fbs_to_number(A,V),fbs_to_number(B,VV),!,VVV is (V /\ \ VV).
merge_fbs([A],B,VVV):-  must_tst(merge_fbs(A,B,VVV)),!.
merge_fbs([A|B],C,VVV):-merge_fbs(A,C,VV),merge_fbs(B,VV,VVV),!.
merge_fbs(A,C,VVV):-fbs_to_number(A,VV),!,must_tst(merge_fbs(VV,C,VVV)),!.
merge_fbs(A,C,VVV):-fbs_to_number(override(A),VV),!,must_tst(merge_fbs(VV,C,VVV)),!.


fbs_to_number(N,O):-number(N),!,N=O.
fbs_to_number(V,VVV):-attvar(V),!,fluent_overriding(V,VV),!,fbs_to_number(VV,VVV).
fbs_to_number(V,O):-var(V),!,V=O.
fbs_to_number([],0).
fbs_to_number(B << A,VVV):-!, fbs_to_number(B,VV), VVV is (VV << A).
fbs_to_number(B+A,VVV):- merge_fbs(+(A),B,VVV),!.
fbs_to_number(B*A,VVV):- merge_fbs(*(A),B,VVV),!.
fbs_to_number(B-A,VVV):- fbs_to_number(B,BB),fbs_to_number(A,AA),VVV is (BB /\ \ AA),!.
fbs_to_number(+(Bit),VVV):-fbs_to_number((Bit),VVV),!.
fbs_to_number(-(Bit),VVV):-fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number(~(Bit),VVV):-fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number( \ (Bit),VVV):-fbs_to_number((Bit),V),!,VVV is ( \ V).
fbs_to_number(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
fbs_to_number((Name),VVV):-bits_for_fluent_default(VV),arg(_,VV,Name=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number((Name),VVV):-bits_for_fluent_default(VV),arg(_,VV,override(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number(override(Name),VVV):-bits_for_fluent_default(VV),arg(_,VV,(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number([A],VVV):-!,fbs_to_number(A,VVV).
fbs_to_number([A|B],VVV):-!,merge_fbs(B,A,VVV).
fbs_to_number(V,VVV) :- VVV is V.



:- module_transparent(w_debug/1).
:- module_transparent(mcc/2).

mcc(G,CU):- !, call_cleanup((G),(CU)).
mcc(G,CU):- G*-> CU ; (once(CU),fail).


w_fbs(M,G):- ('$fluent_default'(W,W),merge_fbs(M,W,N),'$fluent_default'(W,N))->mcc(G,'$fluent_default'(_,W)).

% Call Goal while fluent Var is disabled
wo_fluent(Var,Goal):- 
  get_attr(Var,'$fbs',W),T is W \/ 0x8000,
   while_goal(put_attr(Var,'$fbs',T),Goal,put_attr(Var,'$fbs',W)).


while_goal(Before,Goal,After):-
  set_call_cleanup(true,(Before,Goal,After),After).


wno_dmvars(G):- wno_fluents(wno_debug(G)).
w_dmvars(G):- w_fluents(w_debug(G)).
wno_fluents(G):-  '$fluent_default'(W,W),T is W \/ 0x8000, '$fluent_default'(_,T), call_cleanup(G,'$fluent_default'(_,W)).
w_fluents(G):-  '$fluent_default'(W,W),T is W  /\ \ 0x8000, '$fluent_default'(_,T), call_cleanup(G,'$fluent_default'(_,W)).
wno_debug(G):-  '$fluent_default'(W,W), T is W /\ \ 0x100000 ,  '$fluent_default'(_,T),  call_cleanup(G,'$fluent_default'(_,W)).
w_debug(G):-  '$fluent_default'(W,W),T is W  \/ 0x100000 , '$fluent_default'(_,T), call_cleanup(G,'$fluent_default'(_,W)).

testfv:-forall(test(T),dmsg(passed(T))).

:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),M\=vn,
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A))))
   % ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A))),
   ))).

a1:verify_attributes(_,_,[]).
a2:verify_attributes(_,_,[]).
a3:verify_attributes(_,_,[]).

test(cmp_fbs_variants1):-
  put_attr(X,a1,1),put_attr(X,a2,2),put_attr(X,'$fbs',1),
  put_attr(Y,'$fbs',1),put_attr(Y,a1,1),put_attr(Y,'$fbs',1),
   w_fbs(+variant,X=@=Y).
test(cmp_fbs_variants2):-
 put_attr(X,a1,1),put_attr(X,a2,2),fluent_override(X,+variant),
 fluent_override(Y,+variant),
   w_fbs(+variant,X=@=Y).
test(cmp_fbs_variants3):-
 put_attr(X,'$fbs',1),
 put_attr(Y,'$fbs',1),
   w_fbs(+variant,X=@=Y).



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

:- module(termsink,[memory_var/1,memberchk_same_q/2,mvar_set/2, mvar_getsink/2,mvar_set/2,dont_care/1,
          wno_hooks/1,w_hooks/1,w_hooks/2,
          wno_dmvars/1,w_dmvars/1,
          wno_debug/1,w_debug/1,
  termsink/1,termsource/1,
  memory_sink/1,counter_var/1,sinkbits_to_number/2,  
  anything_once/1,no_bind/1,subsumer_var/1,plvar/1]).
:- set_prolog_flag(access_level,system). 
:- meta_predicate wno_hooks(+).
:- meta_predicate wno_dmvars(+).
:- meta_predicate wno_debug(+).
:- meta_predicate w_hooks(+).
:- meta_predicate w_hooks(+,+).
:- meta_predicate w_dmvars(+).
:- meta_predicate w_debug(+).
:- meta_predicate mcc(0,0).
:- meta_predicate maplist_local(+,+).

:-  [user:library(clpfd)].
:- module_transparent((
  wno_hooks/1,w_hooks/1,w_hooks/2,
  wno_dmvars/1,w_dmvars/1,  
  wno_debug/1,w_debug/1,maplist_local/2)).

% :- '$attvar_default'(W,1), asserta(t_l:save_sinkmode(W)).
 
% /devel/LogicmooDeveloperFramework/swipl-devel/library/termsink
/** <module> Test Module

   Some experiments ongoing

   With any of the above set the system still operates as normal
              until the user invokes  '$attvar_default'/2 to 

   None of these option being enabled will cost more than 
              if( (LD->attrvar.gsinkmode & SOME_OPTION) != 0) ...
  
    
*/

:- meta_predicate w_hooks(+,0),do_test_type(1),wno_hooks(0),must_tst(0),test(?).
:- discontiguous(test/1).
:- nodebug(attvars).
:- nodebug(termsinks).

%% depth_of_var(+Var,-FrameCount) is det.
%
%  if the Variable is on the local stack, FrameCount will tell you for
%  how many levels it has been levels it is away from the creation frame
%
%  This can be a powerfull heuristic in inference engines and 
%  Sat solvers to *help* judge when they are being unproductive.
%  (The example bellow is a loop ... but another idea is that we 
%    can iteratively lengthen the depth allowance of each variable
%   (variable to survive for deeper ))
%
% Example of a different use:
% ==
% q :- q(X), writeln(X).
% q(X) :- depth_of_var(X, D), format('Depth = ~w~n', [D]), D < 5, q(X), notail.
% notail.
% ==
% 
% Running this says:
% ==
% 1 ?- q.
% Depth = 1
% Depth = 2
% Depth = 3
% Depth = 4
% Depth = 5
% false.
% ==
% 

%% anything_once(+Var) is det.
%
% An attributed variable to never be bound to the same value twice
%
%  ==
%  ?- anything_once(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
anything_once(Var):- nonvar(Var) ->true; (get_attr(Var,nr,_)->true;put_attr(Var,nr,old_vals([]))).

nr:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz), \+ memberchk_same_q(VarValue,Waz),nb_setarg(1,AttValue,[VarValue|Waz]).


%% termsink(-X) is det.
%
% Base class of var that consumes terms 
%
termsink(X):-mvar_set(X,+termsink).


%% termsource(-X) is det.
%
% Base class of var that may have a value
%
termsource(X):-mvar_set(X,+termsource).

%% filterterm(-X) is det.
%
% Filter that may produce a term (termsource/1)
%
filterterm(X):-mvar_set(X,+no_bind).

%% nb_no_bind(-X) is det.
%
% Filters terms but stays unbound even after filtering
%
nb_no_bind(X):-mvar_set(X,-on_unify_vmassign+no_bind-no_trail). 

%% dont_care(-X) is det.
%
% nb_no_bind term filter that will bind with anything and call no wakeups
%
dont_care(X):-mvar_set(X,no_wakeup+no_bind-peer_wakeup+no_disable).


%% plvar(-X) is det.
%
% Example of the well known "Prolog" variable!
%
% Using a term sink to emulate a current prolog variable (note we cannot use no_bind)
%
% the code:
% ==
% /* if the new value is the same as the old value accept the unification*/
% plvar(X):- termsource(X),put_attr(X,plvar,binding(X,_)).
% plvar:attr_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar,binding(Var,Value)).
% ==
%
% ==
% ?- plvar(X), X = 1.
% X = 1.
%
% ?- plvar(X), X = 1, X = 2.
% false.
% ==
%
/* if the new value is the same as the old value accept the unification*/
%plvar(X):- mvar_set(X,+no_bind),put_attr(X,plvar,binding(X,_)).
%plvar:attr_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar,binding(Var,Value)).

plvar(X):- put_attr(X,plvar,binding(X,_)).
plvar:verify_attributes(Var,Value,[]):-
      get_attr(Var,plvar,binding(Var,Prev)),
      Value=Prev,
      get_attr(Var,plvar,binding(Var,Value)).


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

subsumer_var(X):- termsource(X),init_accumulate(X,pattern,term_subsumer).


%% counter_var(-X) is det.
%
% Example of:
%
% Using a term sink to add numbers together
%
% ==
% counter_var(X):- termsource(X),init_accumulate(X,numeric,plus).
% ==
% 
% ==
%  ?-  counter_var(X), X= 1, X = 1.
%  X = 2.
% ==
%
counter_var(X):- termsource(X),init_accumulate(X,counter_var,plus).


%% nb_var(+X) is det.
%
% Using prolog variable that is stored as a global (for later use)
%
% nb_var/1 code above doesnt call nb_var/2 (since termsource/1 needs called before call we call format/3 .. promotes a _L666 varable to _G666 )
nb_var(V):- termsource(V), format(atom(N),'~q',[V]),nb_linkval(N,V),put_attr(V,nb_var,N),nb_linkval(N,V).
nb_var:verify_attributes(_Var,N,Value):-
       nb_getval(N,Prev),
       ( % This is how we produce a binding for +termsource "iterator"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % On unification we will update the internal value
             Value=Prev->nb_setval(N,Prev)).

%%  nb_var(+Name,+X) is det.
%
% Using prolog variable that is stored as a global Name (for later use)
% 
%  like nb_linkvar(+Name,+X)
%
%  with the difference that more complex operations are now available at the address 
%  (Like fifdling with the sinkvar props)
%
% ==
%  ?-  nb_var('ForLater',X), member(X,[1,2,3]).
%  X = 1.
%
%  ?- nb_var('ForLater',X).
%  X = 1.
%
%  
% ==
nb_var(N, V):- termsource(V), nb_linkval(N,V),put_attr(V,nb_var,N),nb_linkval(N,V).


%% debug_attvars is det.
%
% Turn on extreme debugging
%
debug_attvars:- sinkmode(+debug_attvars+debug_extreme),!.


%% sinkmode(+Set) is det.
%
% Set system wide sink modes
%
% == 
% ?-listing(bits_for_sinkmode/1) to see them.
% ==
%
%   more to come...
%
sinkmode(X):- var(X),!,'$attvar_default'(X,X).
sinkmode(X):- '$attvar_default'(M,M),merge_sinkmodes(X,M,XM),must_tst('$attvar_default'(_,XM)),!,sinkmode,!.
bits_for_sinkmode(v(
          
         disabled =bit(0), /* allows interp to run recurvely not using the eagers */
         no_bind =bit(1), /* survive bindings to even constants */
         no_trail =bit(2), /* no_trail the attvars previous value */
         no_wakeup =bit(3), /* calling wakeup early to find out if we maybe care */
         peer_trail =bit(4), /* trail any assignment we are about to make on others */
         peer_wakeup =bit(5), /* schedule wakeup on other attvars */
         on_unify_keep_vars =bit(6), /* where unifying with a variable call $wakeup/=bit(1), with the variable  */
         on_unify_linkval =bit(7), /* attempt to linkval to  what  we unify */
         no_inherit =bit(8), /* this term sink doest not inherit the global flags */
         eager_needed =bit(9), /* var needs eager */
         debug_attvars =bit(10), /* print extra debug for ourselves  */
         debug_extreme =bit(11), /* print extra debug for ourselves  */
   
         eager(unify) = eager_bit(16), /*  eager(=) */
         eager(equal) = eager_bit(17), /*  eager(==) call can_unify for equal testing on specialAttibutedVars */
         eager(variant) =eager_bit(18), /*  eager(=@=) */
         eager(unifiable) =eager_bit(19), /*  eager(unifiable) */
         eager(assignment)  =eager_bit(20),  /*  eager(assignment) */
         eager(copy_term) =eager_bit(21), /*  eager(copy_term) */
         eager(compare) =eager_bit(22), /*  eager(compare) */
         eager(bind_const) =eager_bit(23), /* use assignAttvar in assignment even against Variables (if possible)  */
         eager(unify_vp) =eager_bit(24), /* use assignAttvar in assignment even against Variables (if possible)  */
         eager(bind_vp) =eager_bit(25), /* use assignAttvar in assignment even against Variables (if possible)  */    

         override(unify) = override_bit(16), /*  override(=) */
         override(equal) = override_bit(17), /*  override(==) call can_unify for equal testing on specialAttibutedVars */
         override(variant) =override_bit(18), /*  override(=@=) */
         override(unifiable) =override_bit(19), /*  override(unifiable) */
         override(assignment)  =override_bit(20),  /*  override(assignment) */
         override(copy_term) =override_bit(21), /*  override(copy_term) */
         override(compare) =override_bit(22), /*  override(compare) */
         override(bind_const) =override_bit(23), /* use assignAttvar in assignment even against Variables (if possible)  */
         override(unify_vp) =override_bit(24), /* use assignAttvar in assignment even against Variables (if possible)  */
         override(bind_vp) =override_bit(25), /* use assignAttvar in assignment even against Variables (if possible)  */    
            
         no_vmi =bit(29), /* direct LD->slow_unify to be true for us to work */
         vmi_ok =bit(30), /* direct LD->slow_unify is optional */
         
         eager(=)  = eager(unify),
         eager(==)  = eager(equal),
         eager(=@=)  = eager(variant),
         eager(can_unify)  = eager(unifiable),
         eager(\=)  = eager(unifiable),
         eager(\=@=)  = eager(variant),
         eager(\==)  = eager(equal),

         override(=)  = override(unify),
         override(==)  = override(equal),
         override(=@=)  = override(variant),
         override(can_unify)  = override(unifiable),
         override(\=)  = override(unifiable),
         override(\=@=)  = override(variant),
         override(\==)  = override(equal),

         eagerly = (+eager(assignment)+eager(variant)+eager(equal)+eager(unifiable)),
         eager_all = (+eagerly+eager(compare)+eager(copy_term)),
         termsink=(no_bind+peer_wakeup+no_inherit),
         termsource=(no_bind+peer_wakeup+no_inherit),
         override(X)= (eager(X)<<16)
    )). 

%% sinkmode is det.
%
% Print the system global modes
%
sinkmode:-'$attvar_default'(M,M),any_to_sinkbits(M,B),format('~N~q.~n',[sinkmode(M=B)]).


%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
eager_all(Var):- mvar_set(Var,+eager_all),eager_all.

%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
eagerly(Var):- mvar_set(Var,+eagerly),eagerly.

%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
no_bind(Var):- mvar_set(Var,+no_bind).


%% eager_all() is det.
%
% Aggressively make attvars unify with non attvars (instead of the other way arround)
%
eagerly:- sinkmode(+eagerly+no_vmi).
eager_all:- sinkmode(+eager_all+no_vmi).
pass_ref:- sinkmode(+on_unify_linkval).
eager_none:-  sinkmode(-eager_all-eagerly).
%% mvar_getsink(Var,BitsOut)
%
% Get a variables sink properties
%
mvar_getsink(Var,BitsOut):- '$attvar_overriding'(Var,_Key,Modes),any_to_sinkbits(Modes,BitsOut),!.


mvar_sinkmode(V,X):-var(X)->mvar_getsink(V,X);mvar_set(V,X).
mvar_sinkmode(V,X,Y):-mvar_getsink(V,X),mvar_set(V,Y).

%% mvar_set(Var,BitsOut)
%
% Set a variables sink properties
%
mvar_set(Var,Modes):-
  ((
   '$attvar_overriding'(Var,Key,Was)->
       (merge_sinkmodes(Modes,Was,Change),'$attvar_override'(Key,Change)); 
   ((must_tst(sinkbits_to_number(Modes,Number)),'$attvar_override'(Var,Number))))).

:-  [swi(boot/attvar)]. 
%% mvar_set(Var,Bits)
%
% Set a variables sink properties
%
new_mvar(Bits,Var):-mvar_set(Var,Bits).

%  counter_var(X),X=1,X=2,w_hooks(eagerly+eager_all+on_unify_linkval,X=Y).


must_tst(G):- G*-> true; throw(must_tst_fail(G)).
must_tst_det(G):- G,deterministic(Y),(Y==true->true;throw(must_tst_fail(G))).

/*

?-  counter_var(X),X=1,X=2,w_hooks(eagerly+eager_all+on_unify_linkval+debug_attvars,X=Y).

vs 

?-  counter_var(X),X=1,X=2,w_hooks(eagerly+eager_all+on_unify_linkval+debug_attvars,X=Y).

*/  

w_hooks(M,G):- ('$attvar_default'(W,W),merge_sinkmodes(M,W,N),T is N  /\ \ 1,'$attvar_default'(W,T))->mcc(G,'$attvar_default'(_,W)).

:- module_transparent(w_debug/1).
:- module_transparent(mcc/2).

mcc(G,CU):- !, call_cleanup((G),(CU)).
mcc(G,CU):- G*-> CU ; (once(CU),fail).

wno_dmvars(G):- wno_hooks(wno_debug(G)).
w_dmvars(G):- w_hooks(w_debug(G)).
wno_hooks(G):-  '$attvar_default'(W,W),T is W \/ 1, '$attvar_default'(_,T), call_cleanup(G,'$attvar_default'(_,W)).
w_hooks(G):-  '$attvar_default'(W,W),T is W  /\ \ 1, '$attvar_default'(_,T), call_cleanup(G,'$attvar_default'(_,W)).
wno_debug(G):-  '$attvar_default'(W,W), T is W /\ \ 1024 ,  '$attvar_default'(_,T),  call_cleanup(G,'$attvar_default'(_,W)).
w_debug(G):-  '$attvar_default'(W,W),T is W  \/ 1024 , '$attvar_default'(_,T), call_cleanup(G,'$attvar_default'(_,W)).



vartypes_to_test(F):-wno_dmvars((current_predicate(termsink:F/1),functor(P,F,1),predicate_property(P,number_of_clauses(_)),termsink:'$pldoc'(F/1,_,_,_),
  clause(P,(A,_BODY)),compound(A),A=mvar_set(_,_))).
vartypes_to_test(new_mvar(Type)):-wno_dmvars(( bits_for_sinkmode(ALL),arg(_,ALL,Type))).

do_test(test_for(Type)):-
  wno_dmvars((vartypes_to_test(Type))) *-> w_debug(ignore((w_hooks(do_test_type(Type)),fail))) ; do_test_type(Type).


init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).


init_accumulate(Var,M,P):-put_attr(Var,accume,init_accumulate(Var,M,P)).

accume:verify_attributes(Var,Value,[]):- get_attr(Var,accume,Attr),accum_hook(Attr,Value).

% we have our first value!
accum_hook(init_accumulate(Var,M,P),Value):- nonvar(Value),!,put_attr(Var,accume,accume_value(Var,M,P,Value)).
% some other attribute module is trolling us (make no internal changes)
accum_hook(init_accumulate(_,_,_),Value):- !,var(Value).
% we have our subsummer job 
accum_hook(accume_value(Var,M,P,Prev),Value):- nonvar(Value),!,call(P, Prev,Value,Combined),put_attr(Var,accume,accume_value(Var,M,P,Combined)).
% Someone passed a variable and we are a "termsource" (this is the singal to drain the bilge)
accum_hook(accume_value(_Var,_M,P,Prev),Value):-  var(Value),!, nonvar(P), wno_hooks(Prev=Value).


accume:attr_unify_hook(Prev,Value):-
 wno_dmvars(( write_term(accume_unify(Prev,Value),[attributes(portray),ignore_ops(true),quoted(true)]),nl,
  accum_hook(Prev,Value))).


% ?- do_test_type(var).


do_test_type(Type):- writeln(maplist_local=Type+X),  
   call(Type,X),
  maplist_local(=(X),[1,2,3,3,3,1,2,3]),
  writeln(value=X),
  writeln(value=X),var_info(X).
  

do_test_type(Type):- 
  once((writeln(vartype=call(Type,X)),  
      call(Type,X),
      ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(Type=X),
      ignore((get_attrs(X,Ats),writeln(Ats=X))),
      fail)),
      writeln(value=X))),var_info(X).

tv123(B):-mvar_set(X,B),t123(X).
t123(X):- print_var(xbefore=X),L=link_term(X,Y,Z),dmsg(before=L),
  ignore((
   X=1,X=1,ignore(show_call(X=2)),w_debug(Y=X),w_debug(X=Z),print_var(x=X),
   print_var(y=Y),print_var(z=Z),ignore(show_call(X=2)),dmsg(each=L),fail)),
   dmsg(after=L).

maplist_local(G,List):-List==[]->!;(List=[H|T],must_tst(call(G,H)),maplist_local(G,T)).

:- debug(attvars).

var_info(V):- wno_dmvars(show_var(V)).
print_var(V):-wno_dmvars(show_var(V)).
show_var(E):- wno_dmvars((nonvar(E),(N=V)=E, show_var(N,V))),!.
show_var(V):- wno_dmvars((show_var(var_was,V))).

show_var(N,V):- wno_dmvars(((((\+ attvar(V)) -> dmsg(N=V); (must_tst(('$attvar_overriding'(V,Key,C),get_attrs(V,Attrs),any_to_sinkbits(C,Bits))),dmsg(N=(V={Key,Attrs,C,Bits}))))))).


'$source':attr_unify_hook(X,Y):- ignore((debug(termsinks,'~N~q.~n',['$source':attr_unify_hook(X,Y)]))),fail.
'$source':attr_unify_hook(_,Y):- member(Y,[default1,default2,default3])*->true;true.

contains_bit(Var,Bit):- var(Bit),'$attvar_overriding'(Var,_,M),any_to_sinkbits(M,Bits),!,member(Bit,Bits).
contains_bit(Var,Bit):-'$attvar_overriding'(Var,_,M),sinkbits_to_number(Bit,N),!,N is N /\ M.

test123:verify_attributes(Var,_Value,[]):- member(Var,[default1,default2,default3]).
% test123:attr_unify_hook(_,Value):- member(Value,[default1,default2,default3]).


'$ident':verify_attributes(Var,Value,[]):- var(Var),contains_bit(Var,on_unify_next),var(Value),!,member(Value,[default1,default2,default3]).

'$ident':attr_unify_hook(Var,Value):- 
  wno_dmvars((((ignore((var(Var),get_attrs(Var,Attribs), 
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook({var=Var,attribs=Attribs},{value=Value})]))))))).

:-  debug(termsinks).

any_to_sinkbits(BitsIn,BitsOut):-  
 sinkbits_to_number(BitsIn,Mode),
   Bits=[Mode],bits_for_sinkmode(MASKS),
   ignore((arg(_,MASKS,(N=V)),nonvar(V),sinkbits_to_number(V,VV), VV is VV /\ Mode , nb_extend_list(Bits,N),fail)),!,
   BitsOut = Bits.


nb_extend_list(List,E):-arg(2,List,Was),nb_setarg(2,List,[E|Was]).



merge_sinkmodes(V,VV,VVV):-number(V),catch((V < 0),_,fail),!, V0 is - V, merge_sinkmodes(-(V0),VV,VVV),!.
merge_sinkmodes(V,VV,VVV):-number(V),number(VV),VVV is (V \/ VV).
merge_sinkmodes(V,VV,VVV):-var(V),!,V=VV,V=VVV.
merge_sinkmodes(set(V),_,VVV):-sinkbits_to_number(V,VVV),!.
merge_sinkmodes(V,VV,VVV):-var(VV),!, sinkbits_to_number(V,VVV),!.
merge_sinkmodes(+(A),B,VVV):- must_tst((sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V \/ VV))).
merge_sinkmodes(*(A),B,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ VV).
merge_sinkmodes(-(B),A,VVV):- sinkbits_to_number(A,V),sinkbits_to_number(B,VV),!,VVV is (V /\ \ VV).
merge_sinkmodes([A],B,VVV):-  must_tst(merge_sinkmodes(A,B,VVV)),!.
merge_sinkmodes([A|B],C,VVV):-merge_sinkmodes(A,C,VV),merge_sinkmodes(B,VV,VVV),!.
merge_sinkmodes(A,C,VVV):-sinkbits_to_number(A,VV),!,must_tst(merge_sinkmodes(VV,C,VVV)),!.
merge_sinkmodes(A,C,VVV):-sinkbits_to_number(eager(A),VV),!,must_tst(merge_sinkmodes(VV,C,VVV)),!.


sinkbits_to_number(N,O):-number(N),!,N=O.
sinkbits_to_number(V,O):-var(V),!,V=O.
sinkbits_to_number([],0).
sinkbits_to_number(B << A,VVV):-!, sinkbits_to_number(B,VV), VVV is (VV << A).
sinkbits_to_number(B+A,VVV):- merge_sinkmodes(+(A),B,VVV),!.
sinkbits_to_number(B*A,VVV):- merge_sinkmodes(*(A),B,VVV),!.
sinkbits_to_number(B-A,VVV):- sinkbits_to_number(B,BB),sinkbits_to_number(A,AA),VVV is (BB /\ \ AA),!.
sinkbits_to_number(+(Bit),VVV):-sinkbits_to_number((Bit),VVV),!.
sinkbits_to_number(-(Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number(~(Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number( \ (Bit),VVV):-sinkbits_to_number((Bit),V),!,VVV is ( \ V).
sinkbits_to_number(eager_bit(Bit),VVV):-!, sinkbits_to_number(bit(Bit),VV),!,VVV is (VV \/ 2^14).  % eager needed
sinkbits_to_number(override_bit(Bit),VVV):-!, Bit4 is Bit + 4, sinkbits_to_number(bit(Bit4),VVV),!.
sinkbits_to_number(bit(Bit),VVV):- number(Bit),!,VVV is 2 ^ (Bit).
sinkbits_to_number((Name),VVV):-bits_for_sinkmode(VV),arg(_,VV,Name=Bit),!,must_tst(sinkbits_to_number(Bit,VVV)),!.
sinkbits_to_number([A],VVV):-!,sinkbits_to_number(A,VVV).
sinkbits_to_number([A|B],VVV):-!,merge_sinkmodes(B,A,VVV).
sinkbits_to_number(V,VVV) :- catch(( VVV is V),_,fail),!.




%% memberchk_same_q( ?X, :TermY0) is semidet.
%
% Uses =@=/2,  except with variables, it uses ==/2.
%
memberchk_same_q(X, List) :- is_list(List),!, \+ atomic(List), C=..[v|List],!,(var(X)-> (arg(_,C,YY),X==YY) ; (arg(_,C,YY),X =@= YY)),!.
memberchk_same_q(X, Ys) :-  nonvar(Ys), var(X)->memberchk_same0(X, Ys);memberchk_same1(X,Ys).
memberchk_same0(X, [Y|Ys]) :-  X==Y  ; (nonvar(Ys),memberchk_same0(X, Ys)).
memberchk_same1(X, [Y|Ys]) :-  X =@= Y ; (nonvar(Ys),memberchk_same1(X, Ys)).

memberchk_same2(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X==Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

memberchk_same3(X, List) :- Hold=hold(List), !,
        repeat, (arg(1,Hold,[Y0|Y0s]) ->
          ( X=@=Y0-> true; (nb_setarg(1,Hold,Y0s),fail)) ; (! , fail)).

memb_r(X, List) :- Hold=hold(List), !, throw(broken_memb_r(X, List)),
         repeat,
          ((arg(1,Hold,[Y|Ys]),nb_setarg(1,Hold,Ys)) -> X=Y ; (! , fail)).



%% memory_var(+Var) is det.
%
% An attributed variable that records it''s past experience
%
% ?- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).
% memory_var=1
% memory_var=2
% memory_var=3
% memory_var=3
% memory_var=3
% memory_var=1
% memory_var=2
% memory_var=3
% get_attrs=att(mv,old_vals([3,2,1,3,3,3,2,1]),[])
%
%  No.
%  ==
mv:attr_unify_hook(AttValue,VarValue):- AttValue=old_vals(Waz),nb_setarg(1,AttValue,[VarValue|Waz]).

memory_var(Var):- nonvar(Var) ->true; (get_attr(Var,mv,_)->true;put_attr(Var,mv,old_vals([]))).

test(memory_var):- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).


%% memory_sink(+Var) is det.
%
%  Makes a variable that remembers all of the previous bindings (even the on ..)
%
%  This is strill to be wtritten
%
% "She'll try anything twice"
%
%  ==
%  ?- memory_sink(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
% memory_sink(Var):-mvar_set(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.
memory_sink(Var):-mvar_set(Var,[]),put_attr(Var,'_',Var),put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.




% :- [src/test_va]. 



/*
:- if((
  exists_source( library(logicmoo_utils)),
  current_predicate(gethostname/1), 
  % fail,
  gethostname(ubuntu))).
*/

:- use_module(library(logicmoo_utils)).

:- debug(_).
:- debug_attvars.
% :- eager_all.
:- debug(termsinks).

:-export(demo_nb_linkval/1).
  demo_nb_linkval(T) :-
           T = nice(N),
           (   N = world,
               nb_linkval(myvar, T),
               fail
           ;   nb_getval(myvar, V),
               writeln(V)
           ).
/*
   :- debug(_).
   :- nodebug(http(_)).
   :- debug(mpred).

   % :- begin_file(pl).


   :- dynamic(sk_out/1).
   :- dynamic(sk_in/1).

   :- read_attvars(true).

   sk_in(avar([vn='Ex',sk='SKF-666'])).

   :- listing(sk_in).

   :- must_tst((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).

*/

v1(X,V) :- mvar_set(V,X),show_var(V).



%:- endif.



:-'$debuglevel'(_,0).


mvar_call(VarFactory,G):-
   wno_dmvars((term_variables(G,Vs),
   maplist(VarFactory,Vs))),trace,w_dmvars(G).


%% set_unifyp(+Pred,?Var) is det.
%
% Create or alter a Prolog variable to have eagered unification
%
% Done with these steps:
% 1) +termsink = Allow to remain a variable after binding with a nonvar
% 2) +termsource = Declares the variable to be a value producing on_unify_next
% 3) Set the unifyp attribute to the Pred.
set_unifyp(Pred,Var):- wno_dmvars((trace,termsource(Var),put_attr(Var,unifyp,binding(Pred,Var,_Uknown)))).

% Our implimentation of a unifyp variable
unifyp:attr_unify_hook(binding(Pred,Var,Prev),Value):-
        % This is how we produce a binding for +termsource "on_unify_next"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % unification we will update the internal value
             Value=Prev->put_attr(Var,plvar,binding(Pred,Var,Value));
         % Check if out eager was ok
             call(Pred,Prev,Value) -> true;
         % Symmetrically if out eager was ok
             call(Pred,Value,Prev)-> true.




ab(a1,b1).
ab(a2,b2).
ab(a3,b3).

xy(x1,y1).
xy(x2,y2).
xy(x3,y3).

equals(a1,x1).
equals(a2,x2).
equals(a3,x3).
equals(b1,y1).
equals(b2,y2).
equals(b3,y3).

q(A,B):-trace,ab(A,B),xy(A,B).

% label_sources

lv:- mvar_call(set_unifyp(equals),q(A,B)),label_sources(A,B),dmsg(q(A,B)).

:- module_transparent(test:verify_attributes/3).

% test:verify_attributes(Var, Attr3, []):- '$module'(M,M),'$set_source_module'(SM,SM),format('~N cm=~q sm=~q ~q.~n',[M,SM,test:verify_attributes(Var, Attr3, -[])]).
% test:attr_unify_hook(TestAttr, Value):- format('~N~q.~n',[test:attr_unify_hook(TestAttr, Value)]).


test:verify_attributes(X, Value, []) :-
    get_attr(X, test, Attr),
    format("~Nverifying: ~w = ~w;  (attr: ~w)\n", [X,Value,Attr]).

/*


?- put_attr(X, test, a), X = a.
verifying: _G389386 = a;  (attr: a)
X = a.


?-  put_attr(X,test, vars(Y)), put_attr(Y,test, vars(X)), [X,Y] = [x,y(X)].
verifying: _G389483 = x;  (attr: vars(_G389490))
verifying: _G389490 = y(x);  (attr: vars(x))


?- VARS = vars([X,Y,Z]), put_attr(X,test, VARS), put_attr(Y,test,VARS), put_attr(Z,test, VARS), [X,Y,Z]=[0,1,2].
verifying: _G389631 = 0;  (attr: vars([_G389631,_G389638,_G389645]))
verifying: _G389638 = 1;  (attr: vars([0,_G389638,_G389645]))
verifying: _G389645 = 2;  (attr: vars([0,1,_G389645]))
VARS = vars([0, 1, 2]),
X = 0,
Y = 1,
Z = 2.


*/


:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),M\=vn,
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).


% :- autoload.

:- listing(wno_debug).
:- listing('$attvar':'$wakeup'/1).
% :- listing('$attvar':'$wakeup0'/1).
% :- listing('$attvar':wno_mvars_attvar/1).
:- debug(_).
:- debug(attvars).

/*

  * eager_needed =bit(11), /* var needs eager */
  * eager(assignment) =bit(16), /*  eager(=) prioritize attVars before vars
             must be set in the global props*/
  * eager(assignment)  =bit(22), /* use assignAttvar in assignment even against Variables (if possible and not a good idea unless you are trying something new) */

?- leash(-all),visible(+unify),trace,notrace(new_mvar(-on_unify_vmassign,V)),put_attr(V, test, a), V = v.
*/ 

t1:- must_tst(rtrace((when(nonvar(X),member(X,[a(1),a(2),a(3)])),!,findall(X,X=a(_),List),List==[a(1),a(2),a(3)]))).

t2:- must_tst(rtrace( (freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant)))).

% :- eagerly.


/* This tells C, even when asked, to not do bindings (yet) 
                      This is to allow the variables to interact with the standard prolog terms, clause databases and foriegn objects.. for example:
                    test:put_attr(Var,+no_bind),jpl_to_string("hi",Var),X="HI",X=['h','i'],
                       Even if verify_attributes succeeds, still do not bind to the value.
                       verify_attributes should in this case 
                       use continuation goals to update some internal state to decides
                       later how it will continue to operate 
                       for exmaple:  It has been unified with 'Red'  and 'Blue' (primary colors) .. 

                        Var='Red',Var='Blue'
   

                       verify_attribute now only unify with purple as a secondary color.
                       
                       and have the vars attributes manipulated yet still remain a Var and able to continue to work with further standard prolog terms
                       (like in the 'Purple' example.      */


/* attempt to linkval and replace whatever  we unify with 
             (we are passed a new variable that is linkvaled into the slot 
              if X_no_trail is set, the structure modification does not backtrack
              if X_peer_trail is set, the new variable is trailed

              that veriable is trailed so we can have that slot become a variable again and then even the orginal binding
              if we bind *that* variable with the original value durring our wakeup
               */



:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),M\=vn,
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).

:-debug_attvars.

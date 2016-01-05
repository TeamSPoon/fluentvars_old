
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

:- module(meta_atts,[
      wno_hooks/1,w_hooks/1,
      w_fbs/2,
        wno_dmvars/1,w_dmvars/1,
  wno_debug/1,w_debug/1,
          matts_default/0,
          testfv/0, 
          % TODO remove  above before master
      matts_override/2,
      matts_overriding/2,
      '$matts_default'/2,
      matts_default/2,
      matts_default/1,
      new_hooks/2,
      matts/1,
      merge_fbs/3,
      any_to_fbs/2,
      fbs_to_number/2]).


/*

SWI-Prolog fluent patch in implements all of the C support! https://github.com/logicmoo/swipl-devel/ ...

An attributed variable can have any number of attributes. The attributes are accessed by their name. Before an attribute can be created and used, it must be declared with the predicate meta_attribute/2. The declaration has the format

meta_attribute(Name, HandlerList)  PROLOG TODO
Name is an atom denoting the attribute name and usually it is the name of the module where this attribute is being created and used. HandlerList is a (possibly empty) list of handler specifications for this attribute (see Section 16.7).

SEE:  http://eclipseclp.org/doc/userman/umsroot100.html 


unify:
the usual unification. The handler procedure is
unify_handler(+Term, ?Attribute [,SuspAttr])
The first argument is the term that was unified with the attributed variable, it is either a non-variable or another attributed variable. The second argument is the contents of the attribute slot corresponding to the extension. Note that, at this point in execution, the orginal attributed variable no longer exists, because it has already been bound to Term. The optional third argument is the suspend-attribute of the former variable; it may be needed to wake the variable’s ’constrained’ suspension list.
The handler’s job is to determine whether the binding is allowed with respect to the attribute. This could for example involve checking whether the bound term is in a domain described by the attribute. For variable-variable bindings, typically the remaining attribute must be updated to reflect the intersection of the two individual attributes. In case of success, suspension lists inside the attributes may need to be scheduled for waking.

If an attributed variable is unified with a standard variable, the variable is bound to the attributed variable and no handlers are invoked. If an attributed variable is unified with another attributed variable or a non-variable, the attributed variable is bound (like a standard variable) to the other term and all handlers for the unify operation are invoked. Note that several attributed variable bindings can occur simultaneously, e.g. during a head unification or during the unification of two compound terms. The handlers are only invoked at certain trigger points (usually before the next regular predicate call). Woken goals will start executing once all unify-handlers are done.

test_unify:   verify_attributes/3 TODO
a unifiability test which is not supposed to trigger constraints propagation. It is used by the not_unify/2 predicate. The handler procedure is
test_unify_handler(+Term, ?Attribute)
where the arguments are the same as for the unify handler. The handler’s job is to determine whether Attribute allows unification with Term (not considering effects of woken goals). During the execution of the handler, the attributed variable may be bound to Term, however when all attribute handlers succeed, all bindings are undone again, and no waking occurs.

compare_instances:  C is done in branch 'tarau' - PROLOG TODO
computation of instance, subsumption and variance relationship, as performed by the built-ins compare_instances/3, instance/2 and variant/2. The handler procedure is
instance_handler(-Res, ?TermL, ?TermR)
and its arguments are similar to the ones of the compare_instances/3 predicate. The handler is invoked with one or both of TermL and TermR being attributed variables. The task of the handler is to examine the two terms, and compute their instance relationship with respect to the extension attribute in question. The handler must bind Res to = iff the terms are variants, < iff TermL is a proper instance of TermR, or > iff TermR is a proper instance of TermL) with respect to the attribute under consideration. If the terms are not unifiable with respect to this attribute, the handler must fail.
Even though one of TermL and TermR is guaranteed to be an attributed variable, they might not have the particular attribute that the handler is concerned with. The handler must therefore be written to correctly deal with all combinations of an attributed (but potentially uninstantiated attribute) variable with any other term.

copy_term:  C is done in branch 'tarau' - PROLOG TODO
the handler is invoked by either copy_term/2 or copy_term_vars/3. The handler procedure is
copy_handler(?AttrVar, ?Copy)
AttrVar is the attributed variable encountered in the copied term, Copy is its corresponding variable in the copy. All extension handlers receive the same arguments. This means that if the attributed variable should be copied as an attributed variable, the handler must check if Copy is still a free variable or if it was already bound to an attributed variable by a previous handler.

suspensions:  PROLOG ONLY - TODO
this handler is invoked by the suspensions/2 predicate to collect all the suspension lists inside the attribute. The handler call pattern is
suspensions_handler(?AttrVar, -ListOfSuspLists, -Tail)
AttrVar is an attributed variable. The handler should bind ListOfSuspLists to a list containing all the attribute’s suspension lists and ending with Tail.

delayed_goals_number:   PROLOG ONLY - TODO
handler is invoked by the delayed_goals_number/2 predicate. The handler call pattern is
delayed_goals_number_handler(?AttrVar, -Number)
AttrVar is the attributed variable encountered in the term, Number is the number of delayed goals occurring in this attribute. Its main purpose is for the first-fail selection predicates, i.e., it should return the number of constraints imposed on the variable.

get_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate get_var_bounds/3 to retrieve information about the lower and upper bound of a numeric variable. The handler should therefore only be defined if the attribute contains that kind of information. The handler call pattern is
get_bounds_handler(?AttrVar, -Lwb, -Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. The handler should bind Lwb and Upb to numbers (any numeric type) reflecting the attribute’s information about lower and upper bound of the variable, respectively. If different attributes return different bounds information, get_var_bounds/3 will return the intersection of these bounds. This can be empty (Lwb > Upb).

set_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate set_var_bounds/3 to distribute information about the lower and upper bound of a numeric variable to all its existing attributes. The handler should therefore only be defined if the attribute can incorporate this kind of information. The handler call pattern is
set_bounds_handler(?AttrVar, +Lwb, +Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. Lwb and Upb are the numbers that were passed to set_var_bounds/3, and the handler is expected to update its own bounds representation accordingly.

print:   DONE
attribute printing in write/1,2, writeln/1,2, printf/2,3 when the m option is specified. The handler procedure is
print_handler(?AttrVar, -PrintAttr)
AttrVar is the attributed variable being printed, PrintAttr is the term which will be printed as a value for this attribute, prefixed by the attribute name. If no handler is specified for an attribute, or the print handler fails, the attribute will not be printed.
The following handlers are still supported for compatibility, but their use is not recommened:

pre_unify:  PROLOG ONLY - TODO
this is another handler which can be invoked on normal unification, but it is called before the unification itself occurs. The handler procedure is
pre_unify_handler(?AttrVar, +Term)
The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.

delayed_goals:  PROLOG ONLY - TODO
this handler is superseded by the suspensions-handler, which should be preferred. If there is no suspensions- handler, this handler is invoked by the obsolete delayed_goals/2 predicate. The handler procedure is
delayed_goals_handler(?AttrVar, ?GoalList, -GoalCont)
AttrVar is the attributed variable encountered in the term, GoalList is an open-ended list of all delayed goals in this attribute and GoalCont is the tail of this list.

*/

% This type-checking predicate succeeds iff its argument is an ordinary free variable, it fails if it is an attributed variable.
free(X):-var(X),\+attvar(X).

% This type-checking predicate succeeds iff its argument is an attributed variable. For other type testing predicates an attributed variable behaves like a variable.
meta(X):- attvar(X).

% A new attribute can be added to a variable using the tool predicate
% add_attribute(Var, Attr).
% An attribute whose name is not the current module name can be added using add_attribute/3 which is its tool body predicate (exported in sepia_kernel). If Var is a free variable, it will be bound to a new attributed variable whose attribute corresponding to the current module is Attr and all its other attributes are free variables. If Var is already an attributed variable and its attribute is uninstantiated, it will b
:- meta_predicate(add_attribute(+,:)).
add_attribute(Var, Attr):- put_atts(Var, Attr).

% TODO  add_attribute(?Var, Attribute, AttrName):- put_atts(Var, Attr).
% add_attribute(Var, Attr).


'$matts':copy_handler(AttrVar, Copy):- duplicate_term(AttrVar,Copy).

:- meta_predicate(get_attribute(+,:)).
get_attribute(Var, Attr):- get_atts(Var, Attr).

% The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. 
% This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, 
% because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.
% pre_unify_handler(AttrVar, Term).

/*

Eclipse 

where Attr is the value obtained from the handler. If there are several handled attributes, all attributes are qualified like in

X{a:A, b:B, c:C}.

*/

% TODO END remove before master
:- meta_predicate must_tst_det(0).
:- meta_predicate must_tst(0).
:- meta_predicate mcc(0,0).
% TODO END remove before master

:- meta_predicate wno_hooks(+).
:- meta_predicate wno_dmvars(+).
:- meta_predicate wno_debug(+).
:- meta_predicate w_hooks(+).
:- meta_predicate w_fbs(+,+).
:- meta_predicate w_dmvars(+).
:- meta_predicate w_debug(+).
:- module_transparent((
  wno_hooks/1,w_hooks/1,w_fbs/2,
  wno_dmvars/1,w_dmvars/1,
  wno_debug/1,w_debug/1)).
 

:- nodebug(matts).

:- multifile(user:matts_hook/4).
:- dynamic(user:matts_hook/4).
user:matts_hook(Pred,Var,Value,RetCode):-dmsg(user:matts_hook(Pred,Var,Value,RetCode)),fail.


% TODO BEGIN remove before master

:- [swi(boot/attvar)].
:- redefine_system_predicate('$attvar': collect_all_va_goal_lists/3).
:- abolish('$attvar': collect_all_va_goal_lists/3).

% Disables extended AttVar/Attvar wakeups and hooks durring processing.

'$attvar':collect_all_va_goal_lists(A,B,C):- wno_hooks(nh_collect_all_va_goal_lists(A,B,C)).

nh_collect_all_va_goal_lists([]) --> [].
nh_collect_all_va_goal_lists(wakeup(Var, Att3s, Value, Rest)) -->
        ['$attvar_assign'(Var,Value)],
	collect_va_goals(Att3s, Var, Value),
        collect_all_va_goal_lists(Rest).

collect_va_goals(att(Module, _AttVal, Rest), Var, Value) -->
	({ attvar(Var) }
	-> 
           % Disables the attvar from further event processing then re-enables the rest of the system
           ({ wo_hooks(Var,w_hooks(Module:verify_attributes(Var, Value, Goals))) },
               collect_va_goals(Rest, Var, Assignment, Value)
           )
        ;
        []).
        
collect_va_goals([],_,_) --> [].


% TODO END remove before master


'$matts_default'(G,S):-'$matts_default'(G,S,I,I).

%%	matts_default(+Get,+Set) is det.
%
% Get/Set system wide matts modes
% Examples:
%
% ==
% ?- matts_default(_,+disable). % Disable entire system
% ==

matts_default(Get,Set):- '$matts_default'(Get,Get),merge_fbs(Set,Get,XM),must_tst('$matts_default'(_,XM)).


%% matts_default(+Set) is det.
%
% Set system wide matts modes
%
% == 
% ?-listing(bits_for_hooks_default/1) to see them.
% ==

matts_default(X):-number(X),!,'$matts_default'(_,X),matts_default.
matts_default(X):- var(X),!,'$matts_default'(X,X).
matts_default(X):- '$matts_default'(M,M),merge_fbs(X,M,XM),must_tst('$matts_default'(_,XM)),!,matts_default,!.


bits_for_hooks_default(v(

/* '$matts' = 18 AttVarBitS: these bits in an prolog accessable  get_attr/3,putt_attr/3 need it fit in valInt()*/
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
  strict_equal     = 0x0400, "Allows AttVars to implement their own structurally equivalence",
  at_equals        = 0x0800, "Allows AttVars to implement their own variant-ness",
  no_inherit     =  0x1000, "This AttVar doest not inherit from matts_default flags (otherwise they are or-ed)",
  copy_term      =  0x2000, "UNUSED override(copy_term) would allow AttVars to implement their own copy.. (for constants like EmptySinkAttVars)",
  compare        =  0x4000, "UNUSED override(compare) would allow AttVars to decide their non-standard ordering against each other",
  disabled       =  0x8000, "Treat this AttVar as a plain attributed variable (allow the system to operate recusively.. implies no_inherit) ",
  check_vmi      = 0x010000, "LD->slow_unify might need tp be true for us to work (mostly for testing)",
  vmi_ok         = 0x030000, "LD->slow_unify is/was not needed",
  save_wakeup    = 0x040000, "saveWakeup before scheduling",
  immediate      = 0x080000, "run foreignWakeup immediatly after schedule",
  spy            = 0x100000, "spy on matts",
  debug          = 0x100000, "spy on matts",


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

%% matts_default is det.
%
% Print the system global modes
%
matts_default:-'$matts_default'(M,M),any_to_fbs(M,B),format('~N~q.~n',[matts_default(M=B)]).


%% debug_hooks is det.
%
% Turn on extreme debugging
%
debug_hooks(true):-!, matts_default(+debug_hooks+debug_extreme).
debug_hooks(_):- matts_default(-debug_hooks-debug_extreme).

%%    matts_overriding(AttVar,BitsOut)
%
% Get matts properties
%

matts_overriding(AttVar,BitsOut):- wno_hooks(get_attr(AttVar,'$matts',Modes)->any_to_fbs(Modes,BitsOut);BitsOut=0).


%%    matts_override(AttVar,BitsOut)
%
% Set matts properties
%

matts_override(AttVar,Modes):-
 wno_hooks((var(AttVar),
  ((
   get_attr(AttVar,'$matts',Was)->
       (merge_fbs(Modes,Was,Change),put_attr(AttVar,'$matts',Change)); 
   (fbs_to_number(Modes,Number),put_attr(AttVar,'$matts',Number)))))),!.


%%    matts(+AttVar)
%
% Checks to see if a term has matts

has_hooks(AttVar):-wno_hooks(get_attr(AttVar,'$matts',_)).

%%    new_hooks(+Bits,-AttVar) is det.
%
% Create new matts with a given set of Overrides

new_hooks(Bits,AttVar):-matts_override(AttVar,Bits).

:- '$matts':export('$matts':verify_attributes/3).
:- export('$matts':verify_attributes/3).

'$matts':verify_attributes(_,_,[]).

contains_fbs(AttVar,Bit):- any_to_fbs(AttVar,Bits),!,member(Bit,Bits).

any_to_fbs(BitsIn,BitsOut):-  
 fbs_to_number(BitsIn,Mode),
   Bits=[Mode],bits_for_hooks_default(MASKS),
   ignore((arg(_,MASKS,(N=V)),nonvar(V),fbs_to_number(V,VV), VV is VV /\ Mode , matts_vars:nb_extend_list(Bits,N),fail)),!,
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
fbs_to_number(V,VVV):-attvar(V),!,matts_overriding(V,VV),!,fbs_to_number(VV,VVV).
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
fbs_to_number((Name),VVV):-bits_for_hooks_default(VV),arg(_,VV,Name=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number((Name),VVV):-bits_for_hooks_default(VV),arg(_,VV,override(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number(override(Name),VVV):-bits_for_hooks_default(VV),arg(_,VV,(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number([A],VVV):-!,fbs_to_number(A,VVV).
fbs_to_number([A|B],VVV):-!,merge_fbs(B,A,VVV).
fbs_to_number(V,VVV) :- VVV is V.



:- module_transparent(w_debug/1).
:- module_transparent(mcc/2).

mcc(G,CU):- !, call_cleanup((G),(CU)).
mcc(G,CU):- G*-> CU ; (once(CU),fail).


w_fbs(M,G):- ('$matts_default'(W,W),merge_fbs(M,W,N),'$matts_default'(W,N))->mcc(G,'$matts_default'(_,W)).

% Call Goal while matts Var is disabled
wo_hooks(Var,Goal):- 
  get_attr(Var,'$matts',W),T is W \/ 0x8000,
   while_goal(put_attr(Var,'$matts',T),Goal,put_attr(Var,'$matts',W)).


while_goal(Before,Goal,After):-
  set_call_cleanup(true,(Before,Goal,After),After).


wno_dmvars(G):- wno_hooks(wno_debug(G)).
w_dmvars(G):- w_hooks(w_debug(G)).
wno_hooks(G):-  '$matts_default'(W,W),T is W \/ 0x8000, '$matts_default'(_,T), call_cleanup(G,'$matts_default'(_,W)).
w_hooks(G):-  '$matts_default'(W,W),T is W  /\ \ 0x8000, '$matts_default'(_,T), call_cleanup(G,'$matts_default'(_,W)).
wno_debug(G):-  '$matts_default'(W,W), T is W /\ \ 0x100000 ,  '$matts_default'(_,T),  call_cleanup(G,'$matts_default'(_,W)).
w_debug(G):-  '$matts_default'(W,W),T is W  \/ 0x100000 , '$matts_default'(_,T), call_cleanup(G,'$matts_default'(_,W)).

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
  put_attr(X,a1,1),put_attr(X,a2,2),put_attr(X,'$matts',1),
  put_attr(Y,'$matts',1),put_attr(Y,a1,1),put_attr(Y,'$matts',1),
   w_fbs(+variant,X=@=Y).
test(cmp_fbs_variants2):-
 put_attr(X,a1,1),put_attr(X,a2,2),matts_override(X,+variant),
 matts_override(Y,+variant),
   w_fbs(+variant,X=@=Y).
test(cmp_fbs_variants3):-
 put_attr(X,'$matts',1),
 put_attr(Y,'$matts',1),
   w_fbs(+variant,X=@=Y).




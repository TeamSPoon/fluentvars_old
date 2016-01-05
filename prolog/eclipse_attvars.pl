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

/*  realized porting atts.pl (to C) takes me about 14 hours (Jan proably 1/2 hour or less)
   mainly do to destructuring of compounds and undornments (an sometimes adornments of Mod:Attr).  
   Doing it for foriegn itnerface PL_unify_functor(term_t) would only take me 2 hours
    But I didnt trust that the FI method was easy going to be the speed we wanted
   my second hour I was only at 100 lines of C with 600 more to go

  pl2am.pl (DONE) +  am2j.pl (converting to C macros for SWI about total of 8 hours )..  
  second option is much more wise
*/

:- module(meta_atts,[
      matts/0,
      testfv/0, 
      test/1,
      w_debug/1,
      w_dmvars/1,
      w_hooks/1,
      wi_atts/2,
      wo_hooks/2,
      wno_debug/1,
      wno_dmvars/1,
      wno_hooks/1,
      % TODO remove  above before master
      '$matts_default'/2,
      any_to_fbs/2,
      has_hooks/1,
      matts/1,
      matts/2,
      matts_override/2,
      matts_overriding/2,
      merge_fbs/3,
      new_matts/2,
      fbs_to_number/2,
      'meta_attribute'/2,
      set_dict_attvar_reader/1,
      dict_attvar/1,
      dict_attvar/2,
      get_pairs/2,
      put_pairs/2]).

:- meta_predicate('meta_attribute'(+,:)).
:- meta_predicate(get_pairs(+,:)).
:- meta_predicate(put_pairs(+,:)).
:- meta_predicate(dict_attvar(:)).
:- meta_predicate(dict_attvar(:,-)).
:- meta_predicate wi_atts(+,0).

:- meta_predicate w_hooks(0).
:- meta_predicate wno_hooks(0).
:- meta_predicate w_dmvars(0).
:- meta_predicate wno_dmvars(0).
:- meta_predicate w_debug(0).
:- meta_predicate wno_debug(0).

\
% TODO BEGIN remove before master

:- meta_predicate must_tst_det(0).
:- meta_predicate must_tst(0).
:- meta_predicate mcc(0,0).

:- ensure_loaded(library(logicmoo_utils)). % General debug/analyze utils

:- use_listing_vars. % hacks listing/N to show us the source variable names

:- [swi(boot/attvar)]. % pick up changes without re-install


:- redefine_system_predicate('$attvar': collect_all_va_goal_lists/3).
:- abolish('$attvar': collect_all_va_goal_lists/3).

% Disables extended AttVar/Attvar wakeups and hooks durring processing (re-enabled microly per some hooks).
'$attvar':collect_all_va_goal_lists(A,B,C):- wno_hooks(nh_collect_all_va_goal_lists(A,B,C)).

nh_collect_all_va_goal_lists([]) --> [].
nh_collect_all_va_goal_lists(wakeup(Var, Att3s, Value, Rest)) -->
        ['$attvar_assign'(Var,Value)],
	nh_collect_va_goals(Att3s, Var, Value),
        nh_collect_all_va_goal_lists(Rest).

% Disables the attvar from further event processing but re-enables the rest of the system disabled above
nh_collect_va_goals(att(Module, _AttVal, Rest), Var, Value) -->
	({ attvar(Var),Var\==Value }
	-> 
           ({ wo_hooks(Var,w_hooks(Module:verify_attributes(Var, Value, Goals))) },
              '$attvar':goals_with_module(Goals, Module),
               nh_collect_va_goals(Rest, Var, Value)
           )
        ;
        []).
        
nh_collect_va_goals([],_,_) --> [].



/*

SWI-Prolog fluent patch in implements all of the C support! https://github.com/logicmoo/swipl-devel/

*/

% TODO END remove before master



:- use_module(library(ordsets)).


/*
unify:
the usual unification. The handler procedure is
unify_handler(+Term, ?Attribute [,SuspAttr])
The first argument is the term that was unified with the attributed variable, it is either a non-variable or another attributed variable. The second argument is the contents of the attribute slot corresponding to the extension. Note that, at this point in execution, the orginal attributed variable no longer exists, because it has already been bound to Term. The optional third argument is the suspend-attribute of the former variable; it may be needed to wake the variable’s ’constrained’ suspension list.
The handler’s job is to determine whether the binding is allowed with respect to the attribute. This could for example involve checking whether the bound term is in a domain described by the attribute. For variable-variable bindings, typically the remaining attribute must be updated to reflect the intersection of the two individual attributes. In case of success, suspension lists inside the attributes may need to be scheduled for waking.
If an attributed variable is unified with a standard variable, the variable is bound to the attributed variable and no handlers are invoked. If an attributed variable is unified with another attributed variable or a non-variable, the attributed variable is bound (like a standard variable) to the other term and all handlers for the unify operation are invoked. Note that several attributed variable bindings can occur simultaneously, e.g. during a head unification or during the unification of two compound terms. The handlers are only invoked at certain trigger points (usually before the next regular predicate call). Woken goals will start executing once all unify-handlers are done.
*/
meta_handler_name(unify).

/*
test_unify:   REDIRECT ==  verify_attributes/3 TODO
a unifiability test which is not supposed to trigger constraints propagation. It is used by the not_unify/2 predicate. The handler procedure is
test_unify_handler(+Term, ?Attribute)
where the arguments are the same as for the unify handler. The handler’s job is to determine whether Attribute allows unification with Term (not considering effects of woken goals). During the execution of the handler, the attributed variable may be bound to Term, however when all attribute handlers succeed, all bindings are undone again, and no waking occurs.
*/
meta_handler_name(test_unify).

/*
compare_instances:  C is done in branch 'eclipse_c' - PROLOG TODO
computation of instance, subsumption and variance relationship, as performed by the built-ins compare_instances/3, instance/2 and variant/2. The handler procedure is
instance_handler(-Res, ?TermL, ?TermR)
and its arguments are similar to the ones of the compare_instances/3 predicate. The handler is invoked with one or both of TermL and TermR being attributed variables. The task of the handler is to examine the two terms, and compute their instance relationship with respect to the extension attribute in question. The handler must bind Res to = iff the terms are variants, < iff TermL is a proper instance of TermR, or > iff TermR is a proper instance of TermL) with respect to the attribute under consideration. If the terms are not unifiable with respect to this attribute, the handler must fail.
Even though one of TermL and TermR is guaranteed to be an attributed variable, they might not have the particular attribute that the handler is concerned with. The handler must therefore be written to correctly deal with all combinations of an attributed (but potentially uninstantiated attribute) variable with any other term.
*/
meta_handler_name(compare_instances).

/*
copy_term:  C is done in branch 'eclipse_c' - PROLOG TODO
the handler is invoked by either copy_term/2 or copy_term_vars/3. The handler procedure is
copy_handler(?AttrVar, ?Copy)
AttrVar is the attributed variable encountered in the copied term, Copy is its corresponding variable in the copy. All extension handlers receive the same arguments. This means that if the attributed variable should be copied as an attributed variable, the handler must check if Copy is still a free variable or if it was already bound to an attributed variable by a previous handler.
*/
meta_handler_name(copy_term).
meta_handler_name(copy_term_nat).

/*
suspensions:  REDIRECT ==  attribute_goals//1
this handler is invoked by the suspensions/2 predicate to collect all the suspension lists inside the attribute. The handler call pattern is
suspensions_handler(?AttrVar, -ListOfSuspLists, -Tail)
AttrVar is an attributed variable. The handler should bind ListOfSuspLists to a list containing all the attribute’s suspension lists and ending with Tail.
*/
meta_handler_name(suspensions).

/*
delayed_goals_number:   REDIRECT ==  attribute_goals//1 (count)
handler is invoked by the delayed_goals_number/2 predicate. The handler call pattern is
delayed_goals_number_handler(?AttrVar, -Number)
AttrVar is the attributed variable encountered in the term, Number is the number of delayed goals occurring in this attribute. Its main purpose is for the first-fail selection predicates, i.e., it should return the number of constraints imposed on the variable.
*/
meta_handler_name(delayed_goals_number).

/*
get_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate get_var_bounds/3 to retrieve information about the lower and upper bound of a numeric variable. The handler should therefore only be defined if the attribute contains that kind of information. The handler call pattern is
get_bounds_handler(?AttrVar, -Lwb, -Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. The handler should bind Lwb and Upb to numbers (any numeric type) reflecting the attribute’s information about lower and upper bound of the variable, respectively. If different attributes return different bounds information, get_var_bounds/3 will return the intersection of these bounds. This can be empty (Lwb > Upb).

set_bounds:  OUT OF SCOPE (Should be done in CLP)
This handler is used by the predicate set_var_bounds/3 to distribute information about the lower and upper bound of a numeric variable to all its existing attributes. The handler should therefore only be defined if the attribute can incorporate this kind of information. The handler call pattern is
set_bounds_handler(?AttrVar, +Lwb, +Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. Lwb and Upb are the numbers that were passed to set_var_bounds/3, and the handler is expected to update its own bounds representation accordingly.
*/

/*
print:   REDIRECT ==  portray_attvar/1
attribute printing in write/1,2, writeln/1,2, printf/2,3 when the m option is specified. The handler procedure is
print_handler(?AttrVar, -PrintAttr)
AttrVar is the attributed variable being printed, PrintAttr is the term which will be printed as a value for this attribute, prefixed by the attribute name. If no handler is specified for an attribute, or the print handler fails, the attribute will not be printed.
The following handlers are still supported for compatibility, but their use is not recommened:
*/
meta_handler_name(print).

/*
pre_unify:  REDIRECT ==  verify_attributes/3
this is another handler which can be invoked on normal unification, but it is called before the unification itself occurs. The handler procedure is
pre_unify_handler(?AttrVar, +Term)
The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.
*/
meta_handler_name(pre_unify).

/*
delayed_goals:     REDIRECT == attribute_goals//1
this handler is superseded by the suspensions-handler, which should be preferred. If there is no suspensions- handler, this handler is invoked by the obsolete delayed_goals/2 predicate. The handler procedure is
delayed_goals_handler(?AttrVar, ?GoalList, -GoalCont)
AttrVar is the attributed variable encountered in the term, GoalList is an open-ended list of all delayed goals in this attribute and GoalCont is the tail of this list.
*/
meta_handler_name(delayed_goals).


% auto-define attributes otherwise signal error is undeclared attributes are used
:- create_prolog_flag(atts_declared,auto,[type(atom),keep(true)]).
% Users might need to read docs to decided they rather have auto?
:- set_prolog_flag(atts_declared,true).
% What is all this fuss about?
% We need some answer to what happens when ?- user:put_pairs(Var,+a(1)).
% if attibute a/1 is declared in one module at least we have some sense
% Still doesnt solve the problem when if a/1 is declared in several modules
% Should we use the import_module/2 Dag?
% Still doesnt solve the problem when if a/1 is declared only in one unseen module!
% Though every option is simple to implement, it should be left to programmers to decide with flags/options
% and not left just to those editing these files.  Still we need to pick a default.

/*
SEE:  http://eclipseclp.org/doc/userman/umsroot100.html 
An attributed variable can have any number of attributes. The attributes are accessed by their name. Before an attribute can be created and used, it must be declared with the predicate meta_attribute/2. The declaration has the format

meta_attribute(Name, HandlerList)  PROLOG TODO
Name is an atom denoting the attribute name and usually it is the name of the module where this attribute is being created and used. HandlerList is a (possibly empty) list of handler specifications for this attribute (see Section 16.7).
*/
%%    meta_attribute(Name,+HandlerList).
%
% :- meta_attribute(Name,[HandlerL,..., List]).
%
% where each HandlerList has the form HookName:Functor/Arity.
% Having declared some meta_attribute names, these attributes can be added, 
% updated and deleted from unbound variables using the following two predicates 
%(get_pairs/2 and put_pairs/2) defined in the module atts. 
% For each declared meta_attribute name, any variable can have at most one such meta_attribute (initially it has none).
'meta_attribute'(Base,M:V):- new_meta_attribute(Base,V,M),!.

new_meta_attribute(Base,V,M) :- (var(Base);var(M);var(V)), !, throw(error(instantiation_error,'meta_attribute'(Base,M:V))).
new_meta_attribute(Base,Na/Ar,Mod) :- !, functor(At,Na,Ar),new_meta_attribute(Base,At,Mod).
new_meta_attribute(Base,Mod:ANY,_) :- \+ meta_handler_name(Mod),!, new_meta_attribute(Base,ANY,Mod).
new_meta_attribute(_,[],_).
new_meta_attribute(Base,(At1,At2),M) :- new_meta_attribute(Base,At1,M), new_meta_attribute(Base,At2,M).
new_meta_attribute(Base,[At1|At2],M) :- new_meta_attribute(Base,At1,M), new_meta_attribute(Base,At2,M).

new_meta_attribute(Base,P:At,Mod) :- assertion(meta_handler_name(P)),dynamic(Mod:meta_hook/3),
  (Mod:meta_hook(Base,P,At) -> true; asserta(Mod:meta_hook(Base,P,At))).

new_meta_attribute(Base,At,Mod) :- dynamic(Mod:protobute/3),
  (Mod:protobute(Base,At,_) -> true; 
   ((Mod:protobute(Base,_,Nth)->Nth2 is Nth+1;Nth2=1),asserta(Mod:protobute(Base,At,Nth2)))).


%%    put_pairs(+Var, +AccessSpec)
%
% Sets the attributes of Var according to AccessSpec.
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% The effect of put_pairs/2 are undone on backtracking. 
% (prefix + may be dropped for convenience).
% The prefixes of AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual meta_attribute is set to Attribute. If the actual meta_attribute was already present, it is simply replaced.
%  -(Attribute):
%     The corresponding actual meta_attribute is removed. If the actual meta_attribute is already absent, nothing happens.
%
%  Should we ignore The arguments of Attribute, only the name and arity are relevant? Currently coded to
%
% ==
% ?- m1:put_pairs(Var,+a(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_pairs(V,+a(x1,y1)),m1:put_pairs(V,+b(x1,y1)),m1:put_pairs(V,-a(_,_)),m2:put_pairs(V,+b(x2,y2)).
% put_attr(V, m1, [b(x1, y1)]),
% put_attr(V, m2, [b(x2, y2)]) .

put_pairs(Var,M:Atts):- pair_put(Var,M,Atts).


%%    get_pairs(+Var, ?AccessSpec) 
%
% Gets the attributes of Var according to AccessSpec. 
%  If AccessSpec is unbound, it will be bound to a list of all set attributes of Var. 
%
% Non-variable terms in Var cause a type error. 
%  if curent_prolog_flag(atts_compat,xsb).
%
% AccessSpec is either +(Attribute), -(Attribute), or a list of such 
% (prefix + may be dropped for convenience).
%
% The prefixes in the AccessSpec have the following meaning:
%  +(Attribute):
%     The corresponding actual meta_attribute must be present and is unified with Attribute.
%  -(Attribute):
%     The corresponding actual meta_attribute must be absent.
%
%  Should we ignore The arguments of Attribute are ignored, only the name and arity are relevant?
%   yes = XSB_compat, no = less control and perf
%
% ==
% ?- m1:put_pairs(Var,+a(x1,y1)),m1:get_pairs(Var,-missing(x1,y1)).
% put_attr(Var, m1, [a(x1, y1)]).
%
% ?- m1:put_pairs(Var,+a(x1,y1)),m1:get_pairs(Var,X).
% X=[a(x1, y1)],
% put_attr(Var, m1, [a(x1, y1)]).
% ==
% TODO/QUESTION  user:get_pairs(Var,Atts) ->  ??? only attributes in 'user' or all attributes??? Attr=[m1:...]

get_pairs(Var,M:Atts):- pair_get(Var,M,Atts).


pair_exist(_A,_At):- current_prolog_flag(atts_declared,auto),!.
pair_exist(_A,_At):-current_prolog_flag(set_dict_attvar_reader,true),!.
pair_exist(M,At):- \+ \+ (M:dynamic(protobute/3),assertion(M:protobute(M,At,_))).

pair_module(Var,M):- get_attr(Var,M,Was)->assertion(is_list(Was));put_attr(Var,M,[]).

pair_tmpl(At,Tmpl):-functor(At,F,A),functor(Tmpl,F,A).

pair_modulize([], _) --> [].
pair_modulize([G|Gs], M) --> !,
    pair_modulize(G, M),
    pair_modulize(Gs, M).
pair_modulize(G,M)-->
 {strip_module(G,_,GS),
     (G == GS -> MG = M:G ; MG = G)},
 [MG]. 


attrs_to_pairs([])--> [].
attrs_to_pairs(att(M,Att,Rest))-->
   pair_modulize(Att,M),
   attrs_to_pairs(Rest).


% Should 'user' use the import_module/2 Dag? (curretly will just return all)
pair_get(Var,user,Atts):-var(Atts),!,get_attrs(Var,Attr),attrs_to_pairs(Attr,Atts,[]).
% pair_get(Var,M,At):-var(At),!,get_attr(Var,M,At).
pair_get(Var,M,List):-is_list(List),!,maplist(pair_get(Var,M),List).
pair_get(Var,M,+At):- !,pair_get(M,Var,At).
pair_get(Var,_,-(M:At)):- \+ meta_handler_name(M), !,pair_get(Var,M,-At).
pair_get(Var,_, (M:At)):- \+ meta_handler_name(M), !,pair_get(Var,M,At).
pair_get(Var,M,-At):-!,
   pair_exist(M,At),
   (get_attr(Var,M,Cur)->
      \+ memberchk(At,Cur) ;
    true).
pair_get(Var,M,At):-
   pair_exist(M,At),
   (get_attr(Var,M,Cur)->
      memberchk(At,Cur) ;
    fail).


pair_put(_,M,At):-var(At),!,throw(error(instantiation_error,put_pairs(M:At))).
pair_put(Var,M,List):-is_list(List),!,pair_module(Var,M),maplist(pair_put(Var,M),List).
pair_put(Var,M,+At):- !,pair_put(M,Var,At).
pair_put(Var,_,-(M:At)):- \+ meta_handler_name(M),!,pair_put(Var,M,-At).
pair_put(Var,_, (M:At)):- \+ meta_handler_name(M), !,pair_put(Var,M,At).
pair_put(Var,M,-Pair):-!,
  pair_to_att(Pair,Tmpl),
   pair_exist(M,Tmpl),
   (get_attr(Var,M,Cur)->
     (delete(Cur,Tmpl,Upd),put_attr(Var,M,Upd)) ;
    true).
pair_put(Var,M,Pair):-
   pair_to_att(Pair,At),
   pair_exist(M,At),
   (get_attr(Var,M,Cur) ->
    (pair_tmpl(At,Tmpl),
     delete(Cur,Tmpl,Mid), % ord_del_element wont work here because -a(_) stops short of finding a(1).
     ord_add_element(Mid,At,Upd),
     put_attr(Var,M,Upd));
    put_attr(Var,M,[At])).

pair_to_att(Var,Var):-var(Var),!.
pair_to_att(N-V,Tmpl):-!,pair_to_att(N=V,Tmpl).
pair_to_att(N:V,Tmpl):-!,pair_to_att(N=V,Tmpl).
pair_to_att(N=V,Tmpl):-!,assertion(atom(N)),!,Tmpl=..[N,V].
pair_to_att(F/A,Tmpl):-!,assertion((atom(F),integer(A))),functor(Tmpl,F,A).
pair_to_att(Tmpl,Tmpl).

/*

Eclipse 

where Attr is the value obtained from the handler. If there are several handled attributes, all attributes are qualified like in

X{a:A, b:B, c:C}.

*/
set_dict_attvar_reader(X):-set_prolog_flag(set_dict_attvar_reader,X).


dict_attvar(Dict):- dict_attvar(Dict,_),!.
dict_attvar(_:Dict,Out):- \+ compound(Dict),!,Out=Dict.
dict_attvar(Dict,Out):-
   is_dict(Dict),dict_pairs(Dict,M,Pairs),
   (atom(M)->pair_put(Out,M,Pairs);
   (var(M)-> (M=Out,put_pairs(Out,Pairs)))),!.
dict_attvar(Dict,Out):- 
  compound_name_arguments(Dict,F,Args),
   maplist(dict_attvar,Args,ArgsO),!,
   compound_name_arguments(Out,F,ArgsO).

meta_atts:verify_attributes(_,_,[]).

% This type-checking predicate succeeds iff its argument is an ordinary free variable, it fails if it is an attributed variable.
eclipse:free(X):-var(X),\+attvar(X).

% This type-checking predicate succeeds iff its argument is an attributed variable. For other type testing predicates an attributed variable behaves like a variable.
meta(X):- attvar(X).

% A new attribute can be added to a variable using the tool predicate
% add_attribute(Var, Attr).
% An attribute whose name is not the current module name can be added using add_attribute/3 which is its tool body predicate (exported in sepia_kernel). If Var is a free variable, it will be bound to a new attributed variable whose attribute corresponding to the current module is Attr and all its other attributes are free variables. If Var is already an attributed variable and its attribute is uninstantiated, it will b
:- meta_predicate(add_attribute(+,:)).
add_attribute(Var, Attr):- put_atts(Var, Attr).

% TODO  add_attribute(?Var, Attribute, AttrName):- put_atts(Var, Attr).
% add_attribute(Var, Attr).
'$atts':copy_handler(AttrVar, Copy):- duplicate_term(AttrVar,Copy).

:- meta_predicate(get_attribute(+,:)).
get_attribute(Var, Attr):- get_atts(Var, Attr).

% The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. 
% This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, 
% because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.
% pre_unify_handler(AttrVar, Term).

 
:- nodebug(matts).

:- multifile('$atts':matts_hook/4).
:- dynamic('$atts':matts_hook/4).
'$atts':matts_hook(Pred,Var,Value,RetCode):- do_matts_hook(Pred,Var,Value,RetCode).

get_hander(Var,Hook,Handler):- get_attr(Var,Hook,Handler).

% unbind return code
do_matts_hook(Pred,Var,Value,RetCode):-nonvar(RetCode),!,do_matts_hook(Pred,Var,Value,RetCode0),RetCode0=RetCode.
% print debug
do_matts_hook(Pred,Var,Value,RetCode):-notrace((dmsg(user:matts_hook(Pred,Var,Value,RetCode)),fail)).
% Search for handler PER Var
do_matts_hook(Hook,Var,Value,1):-get_hander(Var,Hook,Handler),!,call(Handler,Var,Value).
% 0: == call handler
do_matts_hook(compare,Var,Value,0):- do_matts_hook(==,Var,Value,1),!.
% call back
do_matts_hook(compare,Var,Value,RetCode):- compare(Res,Value,Var),compare_to_retcode(Res,RetCode),!.

do_matts_hook('==',A,B,1):-attrs_val(B,BA),attrs_val(A,AA),BA==AA,!.
do_matts_hook(Hook,A,B,1):-get_val(A,AA),w_hooks(call(Hook,AA,B)).
do_matts_hook('==',A,B,1):-attrs_val(B,BA),attrs_val(A,AA),!,BA=@=AA.
do_matts_hook('=@=',A,B,1):-attrs_val(B,BA),attrs_val(A,AA),!,BA=@=AA.

compare_to_retcode(>,1).
compare_to_retcode(<,-1).
compare_to_retcode(==,0).


attrs_val(Var,AttsO):-'$visible_attrs'(Var,AttsO).


get_val(A,AAA):-get_attr(A,value,AA),!,AA=AAA.
get_val(A,AAA):-get_attr(A,gvar,AA),!,nb_linkval(AA,AAA).
% get_val(A,A).




%%	matts(+Get,+Set) is det.
%
% Get/Set system wide matts modes
% Examples:
%
% ==
% ?- matts(_,+disable). % Disable entire system
% ==

matts(Get,Set):- '$matts_default'(Get,Get),merge_fbs(Set,Get,XM),must_tst('$matts_default'(_,XM)).
'$matts_default'(G,S):-'$matts_default'(G,S,I,I).


%% matts(+Set) is det.
%
% Set system wide matts modes
%
% == 
% ?-listing(fbs_for_hooks_default/1) to see them.
% ==

matts(X):- integer(X),!,'$matts_default'(_,X),matts.
matts(X):- var(X),!,'$matts_default'(X,X).
matts(X):- '$matts_default'(M,M),merge_fbs(X,M,XM),must_tst('$matts_default'(_,XM)),!,matts,!.


fbs_for_hooks_default(v(

/* '$atts' = 18 AttVarBitS: these bits in an prolog accessable  get_attr/3,putt_attr/3 need it fit in valInt()*/
  no_bind              = 0x0001, "C should let wakeup/1 do binding",
  no_wakeup            = 0x0002, "C should skip scheduling a $wakeup/1 ",
  mid_unify            = 0x0004, "do_unify() has called unify",
  peer_wakeup          = 0x0008, "attempt to schedule a wakeup on other attvar peers we unify with",
  peer_trail           = 0x0010, "Those scheduled peers should trail assignment",
  on_unify_keep_vars   = 0x0020, "whenever unifying with a plain variable send the variable to $wakeup/1 as the value",
  unify                = 0x0020, "SAME AS ABOVE used in do_unify()",
  on_unify_replace     = 0x0040, "UNUSED unify replace",
  no_trail             = 0x0080, "Do not bother to trail the previous value",

/* Overrides */
  colon_eq         = 0x0100, "override(unify_vp) like on_unify_keep_vars except happens in unify_vp()",
  bind             = 0x0200, "override(bind_const) like on_unify_keep_vars except happens in bindConst()",
  strict_equal     = 0x0400, "Allows AttVars to implement their own structurally equivalence",
  at_equals        = 0x0800, "Allows AttVars to implement their own variant-ness",
  no_inherit     =  0x1000, "This AttVar doest not inherit from matts flags (otherwise they are or-ed)",
  copy_term      =  0x2000, "override(copy_term) would allow AttVars to implement their own copy.. (for constants like EmptySinkAttVars)",
  copy_term_nat  =  0x2000, "override(copy_term) would allow AttVars to implement their own copy.. (for constants like EmptySinkAttVars)",
  compare        =  0x4000, "UNUSED override(compare) would allow AttVars to decide their non-standard ordering against each other",
  disabled       =  0x8000, "Treat this AttVar as a non attributed variable (allow the system to operate recusively.. implies no_inherit) ",
  check_vmi      = 0x010000, "LD->slow_unify might need tp be true for us to work (mostly for testing)",
  vmi_ok         = 0x030000, "LD->slow_unify is/was not needed",
  return_wake    = 0x040000, "saveWakeup before scheduling",
  nonimmediate   = 0x080000, "run foreignWakeup immediatly after schedule",
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

%% matts is det.
%
% Print the system global modes
%
matts:-'$matts_default'(M,M),any_to_fbs(M,B),format('~N~q.~n',[matts(M=B)]).


%% debug_hooks is det.
%
% Turn on extreme debugging
%
debug_hooks(true):-!, matts(+debug_hooks+debug_extreme).
debug_hooks(_):- matts(-debug_hooks-debug_extreme).

%%    matts_overriding(AttVar,BitsOut)
%
% Get matts properties
%

matts_overriding(AttVar,BitsOut):- wno_hooks(get_attr(AttVar,'$atts',Modes)->any_to_fbs(Modes,BitsOut);BitsOut=0).


%%    matts_override(AttVar,BitsOut)
%
% Set matts properties
%

matts_override(AttVar,Modes):-
 notrace((wno_hooks((var(AttVar),
  ((
   get_attr(AttVar,'$atts',Was)->
       (merge_fbs(Modes,Was,Change),put_attr(AttVar,'$atts',Change)); 
   (fbs_to_number(Modes,Number),put_attr(AttVar,'$atts',Number)))))))),!.


%%    matts(+AttVar)
%
% Checks to see if a term has matts

has_hooks(AttVar):-wno_hooks(get_attr(AttVar,'$atts',_)).

%%    new_matts(+Bits,-AttVar) is det.
%
% Create new matts with a given set of Overrides

new_matts(Bits,AttVar):-notrace((matts_override(AttVar,Bits))).


'$atts':verify_attributes(_,_,[]).

contains_fbs(AttVar,Bit):- any_to_fbs(AttVar,Bits),!,member(Bit,Bits).

% any_to_fbs(Var,BitsOut):- attvar(Var), get_attr(Var,'$mattr',BitsIn),!,any_to_fbs(BitsIn,BitsOut).
any_to_fbs(BitsIn,BitsOut):- notrace((
 must((fbs_to_number(BitsIn,Mode),number(Mode))),
   Bits=[Mode],fbs_for_hooks_default(MASKS),
   ignore((arg(_,MASKS,(N=V)),nonvar(V),nonvar(N),fbs_to_number(V,VV), VV is VV /\ Mode , matts_vars:nb_extend_list(Bits,N),fail)),!,
   BitsOut = Bits)).


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
fbs_to_number(V,O):-var(V),!,0=O.
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
fbs_to_number((Name),VVV):-fbs_for_hooks_default(VV),arg(_,VV,Name=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number((Name),VVV):-fbs_for_hooks_default(VV),arg(_,VV,override(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number(override(Name),VVV):-fbs_for_hooks_default(VV),arg(_,VV,(Name)=Bit),!,must_tst(fbs_to_number(Bit,VVV)),!.
fbs_to_number([A],VVV):-!,fbs_to_number(A,VVV).
fbs_to_number([A|B],VVV):-!,merge_fbs(B,A,VVV).
fbs_to_number(V,VVV) :- VVV is V.


%%    while_goal(Before,Goal,After)
%
% while executing Goal (and each time) run:  once(Before),Goal,After
% But even when goal fails still run After

while_goal(Before,Goal,After):-
  Before,!,
  ( call((Goal,deterministic(T)))
  *-> 
   ( once(After), (T==true -> (dmsg(done),!) ; (true;((Before,fail);fail))))
  ;
  (After,!,fail)
  ).


undo(G):- C=call(G),setup_call_cleanup(true,(true;(G,nb_setarg(1,C,true),fail)),C).


mcc(Goal,CU):- Goal*-> CU ; (once(CU),fail).


%%    wi_atts(Hooks,Goal)
%
% With inherited Hooks call Goal

wi_atts(M,Goal):- notrace(('$matts_default'(W,W),merge_fbs(M,W,N))),!,while_goal('$matts_default'(W,N),Goal,'$matts_default'(_,W)).

%%    wo_hooks(+Var,+Goal)
%
% Without hooks on Var call Goal
wo_hooks(Var,Goal):-
  get_attr(Var,'$atts',W),T is W \/ 0x8000,!,
   while_goal(put_attr(Var,'$atts',T),Goal,put_attr(Var,'$atts',W)).
wo_hooks(_Var,Goal):-Goal.


wno_dmvars(Goal):- wno_hooks(wno_debug(Goal)).
w_dmvars(Goal):- w_hooks(w_debug(Goal)).
wno_hooks(Goal):-  '$matts_default'(W,W),T is W \/ 0x8000, while_goal('$matts_default'(_,T),Goal,'$matts_default'(_,W)).
w_hooks(Goal):-  '$matts_default'(W,W),T is W  /\ \ 0x8000, while_goal('$matts_default'(_,T),Goal,'$matts_default'(_,W)).
wno_debug(Goal):-  '$matts_default'(W,W), T is W /\ \ 0x100000, while_goal('$matts_default'(_,T),Goal,'$matts_default'(_,W)).
w_debug(Goal):-  '$matts_default'(W,W),T is W  \/ 0x100000 , while_goal('$matts_default'(_,T),Goal,'$matts_default'(_,W)).

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

test(cmp_fbs_variants0):- put_attr(X,'$atts',4),put_attr(Y,'$atts',4),wi_atts(+variant,X=@=Y).
test(cmp_fbs_variants0a):- put_attr(X,a1,1),put_attr(X,'$atts',4),put_attr(Y,'$atts',4),wi_atts(+variant,X=@=Y).

test(cmp_fbs_variants1):-
  put_attr(X,a1,1),put_attr(X,a2,2),put_attr(X,'$atts',1),
  put_attr(Y,'$atts',1),put_attr(Y,a1,1),put_attr(Y,'$atts',1),
   wi_atts(+variant,X=@=Y).

test(cmp_fbs_variants2):-
 put_attr(X,a1,1),put_attr(X,a2,2),
 matts_override(X,+variant),
 matts_override(Y,+variant),X=@=Y.

test(cmp_fbs_variants3):-
 put_attr(X,'$atts',1),
 put_attr(Y,'$atts',1),
   wi_atts(+variant,X=@=Y).

:- set_prolog_flag(atts_declared,auto).


system:term_expansion(Dict,X):- current_prolog_flag(set_dict_attvar_reader,true),dict_attvar(Dict,X).
system:goal_expansion(Dict,X):- current_prolog_flag(set_dict_attvar_reader,true),dict_attvar(Dict,X).

% :- set_dict_attvar_reader(true).





/*

SWI-Prolog fluent patch in (though in tarau) implements all of the C support! https://github.com/logicmoo/swipl-devel/ ...

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

get_bounds:  SO FAR UNNEDED
This handler is used by the predicate get_var_bounds/3 to retrieve information about the lower and upper bound of a numeric variable. The handler should therefore only be defined if the attribute contains that kind of information. The handler call pattern is
get_bounds_handler(?AttrVar, -Lwb, -Upb)
The handler is only invoked if the variable has the corresponding (non-empty) attribute. The handler should bind Lwb and Upb to numbers (any numeric type) reflecting the attribute’s information about lower and upper bound of the variable, respectively. If different attributes return different bounds information, get_var_bounds/3 will return the intersection of these bounds. This can be empty (Lwb > Upb).

set_bounds:  SO FAR UNNEDED
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

:- if(current_prolog_flag(fluentvars,true)).
'$fbs':copy_handler(AttrVar, Copy):- duplicate_term(AttrVar,Copy).
:-endif.

:- meta_predicate(get_attribute(+,:)).
get_attribute(Var, Attr):- get_atts(Var, Attr).
get_attribute(X{Name:Attribute},A).

% The first argument is the attributed variable to be unfied, the second argument is the term it is going to be unified with. 
% This handler is provided only for compatibility with SICStus Prolog and its use is not recommended, 
% because it is less efficient than the unify handler and because its semantics is somewhat unclear, there may be cases where changes inside this handler may have unexpected effects.
pre_unify_handler(AttrVar, Term)

/*

Eclipse 

where Attr is the value obtained from the handler. If there are several handled attributes, all attributes are qualified like in

X{a:A, b:B, c:C}.

*/

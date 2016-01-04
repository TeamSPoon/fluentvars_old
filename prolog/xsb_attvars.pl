/*

Example XSB Support

*/

%%    attv_unify(-Var, +Value)
%
% See: http://xsb.sourceforge.net/shadow_site/manual2/node4.html
%
% This is an internal built-in XSB predicate which to is supposed to be used only in the definition 
% of verify_attributes/2. It binds the attributed variable Var to Value without triggering 
% attributed variable interrupt/wakeup. Value is a non-variable term or another attributed variable.
% DM: additionally extended to allow a plain Var
%
attv_unify(Var, Value):- '$attvar_assign'(Var, Value).


% Switches us from verify_attributes/3 to verify_attributes/2 support

% This predicate is called whenever an attributed variable Var (which has at least one attribute) 
% is about to be bound to Value (a non-variable term or another attributed variable). 
% When Var is to be bound to Value, a special interrupt called attributed variable 
% interrupt is triggered, and then XSB's interrupt handler (written in Prolog) calls 
% verify_attributes/2. If it fails, the unification is deemed to have failed. 
% It may succeed non-deterministically, in which case the unification 
% might backtrack to give another answer.
:- module_transparent(system:verify_attributes/3).
system:verify_attributes(Var, Value, []):- 
      context_module(Mod),
      Mod:verify_attributes(Var, Value).
               



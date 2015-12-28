 /** <module> Test Module

   Some experiments ongoing

   With any of the above set the system still operates as normal
              until the user invokes  '$attvar_default'/2 to 

   None of these option being enabled will cost more than 
              if( (LD->attrvar.gsinkmode & SOME_OPTION) != 0) ...
  
    
*/

fluent_call(VarFactory,Goal):-
   term_variables(G,Vs),
   maplist(VarFactory,Vs),
   Goal.


%% set_unifyp(+Pred,?Var) is det.
%
% Create or alter a Prolog variable to have eagered unification
%
% Done with these steps:
% 1) +fluent_sink = Allow to remain a variable after binding with a nonvar
% 2) +fluent_source = Declares the variable to be a value producing on_unify_next
% 3) Set the unifyp attribute to the Pred.
set_unifyp(Pred,Var):- wno_dmvars((trace,fluent_source(Var),put_attr(Var,unifyp,binding(Pred,Var,_Uknown)))).

% Our implimentation of a unifyp variable
unifyp:attr_unify_hook(binding(Pred,Var,Prev),Value):-
        % This is how we produce a binding for +fluent_source "on_unify_next"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % unification we will update the internal value
             Value=Prev->put_attr(Var,plvar,binding(Pred,Var,Value));
         % Check if out eager was ok
             call(Pred,Prev,Value) -> true;
         % Symmetrically if out eager was ok
             call(Pred,Value,Prev)-> true.



:-'$debuglevel'(_,0).


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

lv:- fluent_call(set_unifyp(equals),q(A,B)),label_sources(A,B),dmsg(q(A,B)).

:- module_transparent(test:verify_attributes/3).

% test:verify_attributes(Var, Attr3, []):- '$module'(M,M),'$set_source_module'(SM,SM),format('~N cm=~q sm=~q ~q.~n',[M,SM,test:verify_attributes(Var, Attr3, -[])]).
% test:attr_unify_hook(TestAttr, Value):- format('~N~q.~n',[test:attr_unify_hook(TestAttr, Value)]).



/*
?- 
 asserta((test:verify_attributes(X, Value, [format('~N~q, ~n',[goal_for(Name)])]) :- sformat(Name,'~w',X), get_attr(X, test, Attr),format('~Nverifying: ~w = ~w (attr: ~w),~n', [X,Value,Attr]))).

?- 
 asserta((test:attr_unify_hook(Attr,Value):-format('~N~q, ~n',[test:attr_unify_hook(Attr,Value)]))).



?- 
 put_attr(X, test, a), X = a.
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

?- leash(-all),visible(+unify),trace,notrace(new_fluent(-on_unify_vmassign,V)),put_attr(V, test, a), V = v.
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

% :- debug_attvars.


must_tst(G):- G*-> true; throw(must_tst_fail(G)).
must_tst_det(G):- G,deterministic(Y),(Y==true->true;throw(must_tst_fail(G))).


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

tv123(B):-attvar_override(X,B),t123(X).
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

show_var(N,V):- wno_dmvars(((((\+ attvar(V)) -> dmsg(N=V); (must_tst(('$attvar_overriding'(V,C),get_attrs(V,Attrs),any_to_sinkbits(C,Bits))),dmsg(N=(V={Attrs,C,Bits}))))))).


'$source':attr_unify_hook(X,Y):- ignore((debug(termsinks,'~N~q.~n',['$source':attr_unify_hook(X,Y)]))),fail.
'$source':attr_unify_hook(_,Y):- member(Y,[default1,default2,default3])*->true;true.



%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
eager_all(Var):- attvar_override(Var,+eager_all),eager_all.

%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
eagerly(Var):- attvar_override(Var,+eagerly),eagerly.

%% eager_all(Var) is det.
%
% Aggressively make Var unify with non attvars (instead of the other way arround)
%
no_bind(Var):- attvar_override(Var,+no_bind).


%% eager_all() is det.
%
% Aggressively make attvars unify with non attvars (instead of the other way arround)
%
eagerly:- sinkmode(+eagerly+no_vmi).
noeagerly:- eager_none.
eager_all:- sinkmode(+eager_all+no_vmi).
pass_ref:- sinkmode(+on_unify_linkval).
eager_none:-  sinkmode(-eager_all-eagerly).

test123:verify_attributes(Var,_Value,[]):- member(Var,[default1,default2,default3]).
% test123:attr_unify_hook(_,Value):- member(Value,[default1,default2,default3]).


'$ident':verify_attributes(Var,Value,[]):- var(Var),contains_bit(Var,on_unify_next),var(Value),!,member(Value,[default1,default2,default3]).

'$ident':attr_unify_hook(Var,Value):- 
  wno_dmvars((((ignore((var(Var),get_attrs(Var,Attribs), 
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook({var=Var,attribs=Attribs},{value=Value})]))))))).

:-  debug(termsinks).



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
% memory_sink(Var):-attvar_override(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.
memory_sink(Var):-attvar_override(Var,[]),put_attr(Var,'_',Var),put_attr(Sink,zar,Sink),memory_var(Var),Var=Sink.




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

v1(X,V) :- attvar_override(V,X),show_var(V).



%:- endif.





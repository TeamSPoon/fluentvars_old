/*  Part of SWI-Prolog

    Author:        Douglas R. Miles
    E-mail:        logicmoo@gmail.com 
    WWW:           http://www.swi-prolog.org http://www.prologmoo.com
    Copyright (C): naw...

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
:- module(termsink,[memory_var/1,memberchk_same_q/2,
   
  anything_once/1,termfilter/1,subsumer_var/1,plvar/1]).



 /** <module> Test Module

   Some experiments ongoing

   With any of the above set the system still operates as normal
              until the user invokes  '$fluent_default'/2 to 

   None of these option being enabled will cost more than 
              if( (LD->attrvar.fluent_default & SOME_OPTION) != 0) ...
  
    
*/

:- meta_predicate must_ts_det(0).
:- meta_predicate fluent_call(1,0).


:- user:use_module(library(fluent_vars)).
:- user:use_module(library(atts)).
:- user:use_module(library(eclipse_attvars)).
:- listing('$attvar':'$wakeup'/1).
:- listing('$attvar':collect_all_va_goal_lists//1).
:- debug(_).
:- debug(fluents).
:- debug(attvars).
:- meta_predicate maplist_local(+,+).
:- module_transparent((maplist_local/2)).
:- meta_predicate do_test_type(1),must_ts(0),test(?).

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


%% termfilter(-X) is det.
%
% Filter that may produce a term (termsource/1)
%
termfilter(X):-mvar_set(X,-vmAssign+remainVar).

%% nb_termfilter(-X) is det.
%
% Filters terms but stays unbound even after filtering
%


%% plvar(-X) is det.
%
% Example of the well known "Prolog" variable!
%
% Using a term sink to emulate a current prolog variable (note we cannot use remainVar)
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
%plvar(X):- mvar_set(X,+remainVar),put_attr(X,plvar,binding(X,_)).
%plvar:attr_unify_hook(binding(Var,Prev),Value):-  Value=Prev,put_attr(Var,plvar,binding(Var,Value)).

plvar(X):- put_attr(X,plvar,binding(X,_)).
plvar:verify_attributes(Var,Value,[]):- trace,
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

fluent_call(FluentFactory,Goal):-
   term_variables(Goal,Vs),
   maplist(FluentFactory,Vs),
   Goal.


test:verify_attributes(X, Value, [format('~N~q, ~n',[goal_for(Name)])]) :- sformat(Name,'~w',X), get_attr(X, test, Attr),format('~Nverifying: ~w = ~w (attr: ~w),~n', [X,Value,Attr]).

test:attr_unify_hook(Attr,Value):-format('~N~q, ~n',[test:attr_unify_hook(Attr,Value)]).

:- discontiguous(test/1).


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
nb_var:attr_unify_hook(N,Value):-
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

q(A,B):-ab(A,B),xy(A,B).


%% set_unifyp(+Pred,?Fluent) is det.
%
% Create or alter a Prolog variable to have overrideed unification
%
% Done with these steps:
% 1) +fluent_sink = Allow to remain a variable after binding with a nonvar
% 2) +fluent_source = Declares the variable to be a value producing with on_unify_keep_vars
% 3) Set the unifyp attribute to the Pred.
set_unifyp(Pred,Fluent):- wno_dmvars((trace,fluent_source(Fluent),put_attr(Fluent,unifyp,binding(Pred,Fluent,_Uknown)))).

% Our implimentation of a unifyp variable
unifyp:attr_unify_hook(binding(Pred,Fluent,Prev),Value):-
        % This is how we produce a binding for +fluent_source "on_unify_keep_vars"
          (var(Value),nonvar(Prev)) ->  Value=Prev;
         % same binding (effectively)
             Value==Prev->true;
         % unification we will update the internal value
             Value=Prev->put_attr(Fluent,plvar,binding(Pred,Fluent,Value));
         % Check if out override was ok
             call(Pred,Prev,Value) -> true;
         % Symmetrically if out override was ok
             call(Pred,Value,Prev)-> true.

% label_sources

lv:- fluent_call(set_unifyp(equals),q(A,B)),label_sources(A,B),dmsg(q(A,B)).



:- module_transparent(test:verify_attributes/3).



/*



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





% :- autoload.


t1:- must_ts(rtrace((when(nonvar(X),member(X,[a(1),a(2),a(3)])),!,findall(X,X=a(_),List),List==[a(1),a(2),a(3)]))).

t2:- must_ts(rtrace( (freeze(Foo,setarg(1,Foo,cant)),  Foo=break_me(borken), Foo==break_me(cant)))).

% :- eagerly.


/* This tells C, even when asked, to not do bindings (yet) 
                      This is to allow the variables to interact with the standard prolog terms, clause databases and foriegn objects.. for example:
                    test:put_attr(Fluent,+no_bind),jpl_to_string("hi",Fluent),X="HI",X=['h','i'],
                       Even if verify_attributes succeeds, still do not bind to the value.
                       verify_attributes should in this case 
                       use continuation goals to update some internal state to decides
                       later how it will continue to operate 
                       for exmaple:  It has been unified with 'Red'  and 'Blue' (primary colors) .. 

                        Fluent='Red',Fluent='Blue'
   

                       verify_attribute now only unify with purple as a secondary color.
                       
                       and have the vars attributes manipulated yet still remain a Fluent and able to continue to work with further standard prolog terms
                       (like in the 'Purple' example.      */


/* attempt to linkval and replace whatever  we unify with 
             (we are passed a new variable that is linkvaled into the slot 
              if X_no_trail is set, the structure modification does not backtrack
              if X_peer_trail is set, the new variable is trailed

              that veriable is trailed so we can have that slot become a variable again and then even the orginal binding
              if we bind *that* variable with the original value durring our wakeup
               */




must_ts(G):- G*-> true; throw(must_ts_fail(G)).
must_ts_det(G):- G,deterministic(Y),(Y==true->true;throw(must_ts_fail(G))).

do_test_type(Type):- writeln(maplist_local=Type+X),  
   call(Type,X),
  maplist_local(=(X),[1,2,3,3,3,1,2,3]),
  writeln(value=X),  
  var_info(X).
  

do_test_type(Type):- 
  once((writeln(vartype=call(Type,X)),  
      call(Type,X),
      ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(Type=X),
      ignore((get_attrs(X,Ats),writeln(Ats=X))),
      fail)),
      writeln(value=X))),var_info(X).

tv123(B):-fluent_override(X,B),t123(X).
t123(X):- print_var(xbefore=X),L=link_term(X,Y,Z),dmsg(before=L),
  ignore((
   X=1,X=1,ignore(show_call(X=2)),w_debug(Y=X),w_debug(X=Z),print_var(x=X),
   print_var(y=Y),print_var(z=Z),ignore(show_call(X=2)),dmsg(each=L),fail)),
   dmsg(after=L).

maplist_local(G,List):-List==[]->!;(List=[H|T],must_ts(call(G,H)),maplist_local(G,T)).

:- debug(fluents).

var_info(V):- wno_dmvars(show_var(V)).
print_var(V):-wno_dmvars(show_var(V)).
show_var(E):- wno_dmvars((nonvar(E),(N=V)=E, show_var(N,V))),!.
show_var(V):- wno_dmvars((show_var(var_was,V))).

show_var(N,V):- wno_dmvars(((((\+ attvar(V)) -> dmsg(N=V); (must_ts(('$mvar_get_sinkmode'(V,Key,C),get_attrs(V,Attrs),any_to_fbs(C,Bits))),dmsg(N=(V={Key,Attrs,C,Bits}))))))).


'$source':attr_unify_hook(X,Y):- ignore((debug(termsinks,'~N~q.~n',['$source':attr_unify_hook(X,Y)]))),fail.
'$source':attr_unify_hook(_,Y):- member(Y,[default1,default2,default3])*->true;true.

contains_bit(Var,Bit):- var(Bit),'$mvar_get_sinkmode'(Var,_,M),any_to_fbs(M,Bits),!,member(Bit,Bits).
contains_bit(Var,Bit):-'$mvar_get_sinkmode'(Var,_,M),fbs_to_number(Bit,N),!,N is N /\ M.


'$ident':verify_attributes(Var,Value,Goals):- debug(attvars,'~N~q.~n',['$ident':verify_attributes(Var,Value,Goals)]).

'$ident':attr_unify_hook(Var,Value):- var(Var),contains_bit(Var,iteratorVar),var(Value),!,member(Value,[default1,default2,default3]).
'$ident':attr_unify_hook(Var,Value):- 
  wno_dmvars((((ignore((var(Var),get_attrs(Var,Attribs), 
   debug(termsinks,'~N~q.~n',['$ident':attr_unify_hook({var=Var,attribs=Attribs},{value=Value})]))))))).

% https://github.com/Muffo/aiswi/blob/master/sciff/restrictions.pl

% https://github.com/Muffo/aiswi/blob/master/sciff/quant.pl

%% override_all(Fluent) is det.
%
% Aggressively make Fluent unify with non fluents (instead of the other way arround)
%
override_all(Fluent):- fluent_override(Fluent,+override_all),override_all.

%% override_all(Fluent) is det.
%
% Aggressively make Fluent unify with non fluents (instead of the other way arround)
%
eagerly(Fluent):- fluent_override(Fluent,+eagerly),eagerly.

%% override_all(Fluent) is det.
%
% Aggressively make Fluent unify with non fluents (instead of the other way arround)
%
no_bind(Fluent):- fluent_override(Fluent,+no_bind).


%% override_all() is det.
%
% Aggressively make fluents unify with non fluents (instead of the other way arround)
%
eagerly:- fluent_default(+eagerly+check_vmi).
noeagerly:- override_none.
override_all:- fluent_default(+override_all+check_vmi).
pass_ref:- fluent_default(+on_unify_replace).
override_none:-  fluent_default(-override_all-eagerly).

test123:verify_attributes(Fluent,_Value,[]):- member(Fluent,[default1,default2,default3]).
% test123:attr_unify_hook(_,Value):- member(Value,[default1,default2,default3]).


'$ident':verify_attributes(Fluent,Value,[]):- var(Fluent),contains_bit(Fluent,on_unify_keep_vars),var(Value),!,member(Value,[default1,default2,default3]).

'$ident':attr_unify_hook(Fluent,Value):- 
  wno_dmvars((((ignore((var(Fluent),get_attrs(Fluent,Attribs), 
   debug(fluents,'~N~q.~n',['$ident':attr_unify_hook({var=Fluent,attribs=Attribs},{value=Value})]))))))).

:-  debug(fluents).



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

/*
memb_r(X, List) :- Hold=hold(List), !, throw(broken_memb_r(X, List)),
         repeat,
          ((arg(1,Hold,[Y|Ys]),nb_setarg(1,Hold,Ys)) -> X=Y ; (! , fail)).
*/


%% memory_var(+Fluent) is det.
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
mv:attr_unify_hook(AttValue,FluentValue):- AttValue=old_vals(Waz),nb_setarg(1,AttValue,[FluentValue|Waz]).

memory_var(Fluent):- nonvar(Fluent) ->true; (get_attr(Fluent,mv,_)->true;put_attr(Fluent,mv,old_vals([]))).

test(memory_var):- memory_var(X),  ignore((member(X,[1,2,3,3,3,1,2,3]),writeln(memory_var=X),fail)),get_attrs(X,Attrs),writeln(get_attrs=Attrs).


%% memory_fluent(+Fluent) is det.
%
%  Makes a variable that remembers all of the previous bindings (even the on ..)
%
%  This is strill to be wtritten
%
%  ==
%  ?- memory_fluent(X),member(X,[1,2,3,3,3,1,2,3]).
%  X = 1;
%  X = 2;
%  X = 3;
%  No.
%  ==
% memory_fluent(Fluent):-fluent_override(Sink,[]), put_attr(Sink,zar,Sink),memory_var(Fluent),Fluent=Sink.
memory_fluent(Fluent):-fluent_override(Fluent,[]),put_attr(Fluent,'_',Fluent),put_attr(Sink,zar,Sink),memory_var(Fluent),Fluent=Sink.




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
% :- debug_fluents.
% :- override_all.
:- debug(fluents).

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

   :- must_ts((sk_in(Ex),get_attr(Ex,sk,What),What=='SKF-666')).

*/

v1(X,V) :- fluent_override(V,X),show_var(V).



%:- endif.






:- source_location(S,_),prolog_load_context(module,M),
 forall(source_file(M:H,S),
 ignore((functor(H,F,A),M\=vn,
   \+ predicate_property(M:H,imported_from(_)),
   \+ arg(_,[attr_unify_hook/2,'$pldoc'/4,'$mode'/2,attr_portray_hook/2,attribute_goals/3],F/A),
   \+ atom_concat('_',_,F),
   ignore(((\+ atom_concat('$',_,F),export(F/A)))),
   ignore((\+ predicate_property(M:H,transparent), M:module_transparent(M:F/A)))))).


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
      sink_fluent/1,
      source_fluent/1,
      dc_fluent/1]).



:- nodebug(fluents).


%%	sink_fluent(-Fluent) is det.
%
% Base class of "SinkFluent" that recieves bindings

sink_fluent(Fluent):-put_atts(Fluent,+no_bind).


%%	source_fluent(-Fluent) is det.
%
% Base class of "SourceFluent" that creates bindings

source_fluent(Fluent):-put_atts(Fluent,+no_bind).


%%	dc_fluent(-Fluent) is det.
%
% Create a truely don't care '_' Fluent
% Will unify multiple times and remain a var
% even after binding. At bind with anything and call no wakeups
% peer or otherwise
% Tarau's "EmptySink" matts

dc_fluent(Fluent):-put_atts(Fluent,no_wakeup+no_bind-peer_wakeup+no_disable).



/******************************************************************************
File: in_tail.pl
Author: Louise Dennis

Predicates to control rippling, in particular to prevent rippling in, whilst a 
destructor os some kind is still hanging around.  These work with the wave 
method.

Last Modified: 4th Jun 1997
******************************************************************************/

%% wv_in_in_tail(+Goal, +LHS, +RHS)
%% Succeeds if there is an inward wavefront on the RHS and the LHS has an
%% outermost function which is a destructor.
%%
%% Succeeds if in redution phase
wv_in_in_tail(G, L, R):-
	wave_fronts(UnAnnG, _, G),
	exp_at(UnAnnG, _, TlExp),
	TlExp =.. [act|_].
	
%% pre_pre(+Goal)
%% Succeeds if there is destructor in the goal and the goal if of the form 
%% related(A, B).
pre_pre(G):-
	matrix(_, Phi in _, G),
	Phi =.. [and|List],
	member(A, List),
	wave_fronts(UnAnn, _, A),
	UnAnn =.. [act|_].

tail :- consult('~/xclam/in_tail_lts.pl').

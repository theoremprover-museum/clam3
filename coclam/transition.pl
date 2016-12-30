/*****************************************************************************

     File: transition.pl
     Author: Louise Dennis

 Predicates for use with the transition proof method
******************************************************************************/

/* 1st September, typing information passed to det_goal in order to
guide annotation.  */

/* 8th September, added clause into check_tran_conds checking for
inappropriate transitions in type checking with induction */

 %% PRECONDITIONS


 %%---------------
 %% Precondition 1
 %%---------------
 %% There is a term, Phi, in the goal of the form /\ ai act(alpha) pi
 %%
 %% conj_trans_goal(G, Phi)

 conj_trans_goal(G, ActList):-
	matrix_conds(_, Conds, Term, _, G),
	\+ (member(Exp, Conds), function_defn(Exp, Rule:C=>Exp:=>R)),
	exp_at(Term, _, Phi),
	Phi =.. [and|ActList],
	\+ ActList = [],
	actlist(ActList).
 conj_trans_goal(G, [act(Act)]):-
	matrix_conds(_, Conds, Term, _, G),
	\+ (member(Exp, Conds), function_defn(Exp, Rule:C=>Exp:=>R)),
	\+ (exp_at(Term, _, P), P =.. [and|_]),
	exp_at(Term, _, act(Act)).

 %% actlist(+List) succeeds if all elements of the list are of the form
 %% ai act(alpha) pi

 actlist([]).
 actlist([act(_)|T]):-
	actlist(T).

 %%---------------
 %% Precondition 2
 %%---------------
 %% All the ai are of the form ai = ci(...) where ci is a recognised
 %% constructor in the language.
 %%
 %% cons_in_conj(Phi, ConList)

 %% conslist(+Actlist, -ConList)
 %% succeeds if transitions apply directly to all the terms in actlist

 cons_in_conj(_, _, []).
 cons_in_conj(H, G, [act(Term)|ActTail]):-  %, ConList):-
	transition(Cond, Term, _, _),
	check_tran_conds(Cond, H, G, Term,[]),
	cons_in_conj(H, G, ActTail).

check_tran_conds(Cond, H, G, _, Vs):-
	member(TT:Typ, Cond), member(TT:Type, Vs),
	\+ subtype(Typ,Type), !, fail.  
check_tran_conds(Cond, H, G, _,_):-
	matrix_conds(_, Cs, act(T1) and act(T2), Type, G),
	strip_meta_annotations(T1, TT),
	member(TT:Typ, Cond), \+ subtype(Typ,Type), !, fail.
check_tran_conds(Cond, H, G, _,_):-
	matrix_conds(_, Cs, act(T1) and act(T2), Type, G),
	strip_meta_annotations(T2, TT),
	member(TT:Typ, Cond), \+ subtype(Typ, Type), !, fail.
check_tran_conds(Cond, H, G, type(T, Type),_):-
	member(T:Typ, Cond), \+ subtype(Typ, Type), !, fail.
check_tran_conds(Cond, H, G, type(T, _),_):-
	matrix(_, Term, G),
	sort_conds(Term, _, Type, _),
	\+ (member(X, Cond), (\+member(_:X, [_:T in Type|H]), \+ X=(_:_))).
check_tran_conds(Cond, H, G, type(T, _),_):-
	matrix(_, Term, G),
	sort_conds(Term, _, int, _),
	\+ (member(X, Cond), (\+member(_:X, [_:T in pnat|H]), \+ X=(_:_))).
check_tran_conds(Cond, H, G, T,_):-
	\+ T = type(_, _),
	matrix(_, Term, G),
	sort_conds(Term, _, Type, _),
	\+ (member(X, Cond), (\+member(_:X, [_:T in Type|H]), \+ X=(_:_))).
check_tran_conds(Cond, H, G, T,_):-
	\+ T = type(_, _),
	matrix(_, Term, G),
	sort_conds(Term, _, int, _),
	\+ (member(X, Cond), (\+member(_:X, [_:T in pnat|H]), \+ X=(_:_))).

subtype(T, T).
subtype(T, T1):-subtype_lang(T, T1).

 %%---------------
 %% Precondition 3
 %%---------------
 %% All transitions associated with each term 
 %% act(ai) appearing in Phi are associated with all act(ai) in Phi
 %%
 %% check_transitions(Phi, TransList)

 check_transitions(_, _, [], [], [], []).
 check_transitions(H, G, [act(Term)|T], TransOut, OutT, M1):-
	set_of(Transition-[act(Term)-Target],
	        TargetUnAnn^Ter^Targ^Cond1^Cond2^(
		transition(Cond1, Term, Transition, Target),
		check_tran_conds(Cond1, H, G, Term, [])), Trans),
	set_of_trans(Trans, Ts, TransB, triv), 
	check_transitions(H, G, T, TransA, TsA, _),
	merge_transitions(Ts, TsA, M1, Ts1, []),
	append(M1, Ts1, OutT),
	trans_append(TransB, TransA, TransOut).

merge_transitions(T, [], [], T, []).
merge_transitions([], T, [[T, Acc]], [], Acc):-
	\+ T = [],
	\+ Acc = [].
merge_transitions([H|T], Trans, Out, [H|Out1], Acc):-
	nth(_, Trans, H, Rest),
	merge_transitions(T, Rest, Out, Out1, Acc).
merge_transitions([H|T], Trans, O, Out, Acc):-
	\+ member(H, Trans),
	merge_transitions(T, Trans, O, Out, [H|Acc]).

%% find_target(Ter, Targ, Term, Target,_,_):-
%%	strip_meta_annotations(Term, NoAnn),
%%	NoAnn =.. [F|_],
%%	(var(Ter);(\+var(Ter), Ter =.. [F|_])),
%%	copy_term([Ter, Targ], [TerG, TargG]),
%%	make_ground([TerG, TargG]),
%%	exp_at(TerG, Pos, TargG),
%%	exp_at(Term, Pos, Target), !.
%% find_target(Ter, Targ, Term, Target, Ter, Target):-
%%	copy_term([Ter, Targ], [TerG, TargG]),
%%	make_ground([TerG, TargG]),
%%	\+ exp_at(TerG, _, TargG).

 set_of_trans([], [], [], nontriv).
 set_of_trans([Trans-S|T], [Trans|NewT], [Trans-S|Out], _):-
	\+ member(Trans-_, T),
	set_of_trans(T, NewT, Out, nontriv).
 set_of_trans([Trans-_|T], NewT, Out, Triv):-
	member(Trans-_, T),
	set_of_trans(T, NewT, Out, Triv).

 trans_append(T, [], T).
 trans_append(Trans, [T-S|Tail], Out):-
	nth(_, Trans, T-S1, Rest),
	append(S, S1, S2),
	trans_append([T-S2|Rest], Tail, Out).
 trans_append(Trans, [T-S|Tail], Out):-
	\+ member(T-S, Trans),
	trans_append([T-S|Trans], Tail, Out).

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 %% FORMING GOAL
 %%-------
 %% Step 1
 %%-------
 %% Performed in preconditions.
 %%-------
 %% Step 2
 %%-------
 %% Remove Phi
 %%
 %% remove_phi(Phi, H, G, NewG)

 remove_phi([act(Term)], H, G, H==>NewG):-
	matrix_conds(Vs, Conds, _, Type, G),
	matrix_conds(Vs, Conds, Term, Type, NewG).
 remove_phi(Phi, H, G, H==>NewG):-
	Phi = [act(A), act(B)],
	matrix_conds(Vs, Conds, _, Type, G),
	matrix_conds(Vs, Conds, related(A, B), Type, NewG).

 %%-------
 %% Step 3
 %%-------
 %% Replace all occurence of pi appearing elsewhere in the goal with pik
 %%
 %% replace_tran_subs(NewG, Subslist, Goal)

 replace_tran_subs(H==>NewG, [[A], [B]], Translist, H==>Goal):-
	matrix_conds(Vs, Conds, Term, Type, NewG),
	member(A-SubslistA, Translist), 
	member(B-SubslistB, Translist), 
	do_subs(SubslistA, Term, NewTermA),
	do_subs(SubslistB, NewTermA, NewTerm),
	tran_type(Type, Transition, TT),
	det_goal(H, NewTerm, NewTerm, Vs, AnnTerm, TT),
	see_sinks(Vs, AnnTerm, SinkTerm),
	find_NewG(Type, Transition, Vs, SinkTerm, Goal, Conds).
 replace_tran_subs(H==>NewG, Transition, Translist, H==>Goal):-
	matrix_conds(Vs, Conds, Term, Type, NewG),
	member(Transition-Subslist, Translist), 
	do_subs(Subslist, Term, NewTerm),
	tran_type(Type, Transition, TT),
	det_goal(H, NewTerm, NewTerm, Vs, AnnTerm, TT),
	see_sinks(Vs, AnnTerm, SinkTerm),
	find_NewG(Type, Transition, Vs, SinkTerm, Goal, Conds).

 do_subs(_, [], Term, Term).
 do_subs([act(A)-P], Term, NT):-
	replace_all(A, P, Term, NT).
 do_subs([act(A)-P, act(B)-P1], related(A, B), related(P, P1)).
 do_subs([act(A)-P, act(B)-P1], related(B, A), related(P1, P)).


transition_equalities([], _, _, []).
transition_equalities([[[num(M)], [num(N)]]], H, G, [H==>Goal]):-
	matrix_conds(Vs, Conds, _, Type, G),
	matrix_conds(Vs, Conds, M=N, Type, Goal).
	
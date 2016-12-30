/*************************************************************************
   File:tidy_lam.pl
   Author: Louise Dennis
   Last Modified: 21st August 1997

   Purpose: Predicates for tidying up lambda terms with clam.v3 - with
   coinduction
*************************************************************************/

%% lambda term
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos, lam(_, _) of _),
	exp_at(CTerm, Pos, D),
	wave_fronts(lam(X, Y) of Z, WFronts, D), !,
	exp_at(Term, [2|Pos], DZ),
	exp_at(Term, [2|[1|Pos]], DY),
	exp_at(DY, P, X),
	replace_all(X, DZ, DY, NewY),
	ann(NewY, WFronts, Ann, P),
	replace(Pos, Ann, Term, NTerm),
	tidy_lam(NTerm, NewTerm).

%% f of y (f atomic)
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos,  _ of _),
               % find of term without worring about WF
	exp_at(CTerm, Pos, D),
               % find expression in same place in annotated term
	wave_fronts(Y of Z, WFronts, D),
               % Find the wave fronts
	exp_at(Term, [1|Pos], DY), 
	atomic(DY),
	\+ var(DY), !,
	exp_at(Term, [2|Pos], DZ),
	NewY =.. [DY|[DZ]],
	ann(NewY, WFronts, Ann, [1]),
	replace(Pos, Ann, Term, NTerm),
	tidy_lam(NTerm, NewTerm).

%% s(s) of y 
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos,  Y of _),
	s_seq(Y),
	exp_at(CTerm, Pos, D),
	wave_fronts(Y of Z, WFronts, D),
	s_seq(Y),
	exp_at(Term, [1|Pos], DY), !,
	exp_at(Term, [2|Pos], DZ),
	s_seq(NewY, DY, DZ),
	ann(NewY, WFronts, Ann, [1]),
	replace(Pos, Ann, Term, NTerm),
	tidy_lam(NTerm, NewTerm).

s_seq(s(s)).
s_seq(Y):-
	Y =.. [s|[S]],
	s_seq(S).

s_seq(NewY, s, DZ):-
	NewY =.. [s|[DZ]].
s_seq(NewY, S, DZ):-
	S =.. [s|[Exp]],
	s_seq(Y, Exp, DZ),
	NewY =.. [s|[Y]].

%% ::(x) of y
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos,  ::(_) of _),
	exp_at(CTerm, Pos, D),
	wave_fronts(::(Y) of Z, WFronts, D), !,
	exp_at(Term, [2|Pos], DZ),
	exp_at(Term, [1|[1|Pos]], DY),
	replace(Pos, DY::DZ, Term, NTerm),
	tidy_lam(NTerm, NewTerm).

%% plus(x) of y and times(x) of y
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos,  F of _),
	F =.. [FSym|[Y]],
	\+ FSym =.. mapcar, \+ FSym =.. s, \+ FSym =.. ::,
	exp_at(CTerm, Pos, D),
	wave_fronts(F2 of Z, WFronts, D), !,
	exp_at(Term, [2|Pos], DZ),
	exp_at(Term, [1|[1|Pos]], DY),
	NewTer =.. [FSym|[DY, DZ]],
	replace(Pos, NewTer, Term, NTerm),
	tidy_lam(NTerm, NewTerm).

%% mapcar(x) of y
tidy_lam(Term, NewTerm):-
	copy_term(Term, CTerm),
	make_ground(CTerm),
	strip_meta_annotations(CTerm, UnAnn),
	exp_at(UnAnn, Pos,  mapcar(_) of _),
	exp_at(CTerm, Pos, D),
	wave_fronts(mapcar(Y) of Z, WFronts, D), !,
	exp_at(Term, [2|Pos], DZ),
	exp_at(Term, [1|[1|Pos]], DY),
	replace(Pos, mapcar(DZ, DY), Term, NTerm),
	tidy_lam(NTerm, NewTerm).
tidy_lam(Term, Term).


ann(Term, WHFronts, Ann, P):-
	member([]-[[2]]/D, WHFronts),
	wave_fronts(Term, [[]-[P]/D], Ann).
ann(Term, WHFronts, Ann, P):-
	member([]-[HolePos]/D, WHFronts),
     	wave_fronts(Term, [[]-[]/D], Ann).
ann(Term, WHFronts, Term, _):-
	\+ (member([]-[HolePos]/D, WHFronts),
        append(Res, [2], HolePos)).

tidy:- consult('~/xclam/tidy_lam.pl').




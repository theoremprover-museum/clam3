tidy_appn(T, TAnn, NewG, NumF):-
        exp_at(T, Pos, appn(Num, F, Term)),
	f_in_term(NumF, F, Term, NewTerm),
	\+ NumF = 0,
	myplus(N2, Num, NumF),
	replace(Pos, appn(N2, F, NewTerm), TAnn, NewG).
tidy_appn(T, TAnn, NewG, NumF):-
	T = related(_, _),
        exp_at(T, Pos, Term),
	exp_at(Term, _, appn(Num, F, NewTerm)),
	f_above_term(NumF, F, Term),
	\+ NumF = 0,
	myplus(N2, Num, NumF),
	replace(Pos, appn(N2, F, NewTerm), TAnn, NewG).

f_in_term(0, F, Term, Term):- \+ Term =.. [F|_].
f_in_term(s(N), F, Term, NewTerm):-
	find_outer(F, Term, NTerm),
	f_in_term(N, F, NTerm, NewTerm).

f_above_term(0, F, Term):- \+ Term =.. [F|_].
f_above_term(s(N), F, Term):-
	find_outer(F, Term, NTerm),
	f_above_term_def(N, F, NTerm).
f_above_term_def(0, F, appn(_, F, _)).
f_above_term_def(s(N), F, Term):-
	find_outer(F, Term, NTerm),
	f_above_term_def(N, F, NTerm).

myplus(N, N, 0).
myplus(M, N1, s(N2)):-
	myplus(N, N1, N2),
	wave_fronts(s(N), [[]-[[1]]/[hard, in]], M).

appn:-consult('~/xclam/tidy_appn.pl').

find_outer(F, Term, NTerm):-
	atomic(F), Term =.. [F|[NTerm]].
find_outer(S, Term, NTerm):-
	s_seq(S),
	s_seq1(Term, S, NTer).
find_outer(F, Term, NTerm):-
	\+ s_seq(F),
	F =.. [Func|List],
	\+ Func = mapcar,
	Term =.. [Func|TermList],
	reverse(TermList, [NTerm|RevList]).
find_outer(F, Term, NTerm):-
	F =.. [mapcar|List],
	\+ Func = mapcar,
	Term =.. [Func|[NTerm|TermList]].
	
s_seq1(Term, s, DZ):- Term =.. [s|[DZ]].
s_seq1(NewY, S, DZ):-
	S =.. [s|[Exp]],
	NewY =.. [s|[Y]],
	s_seq1(Y, Exp, DZ).

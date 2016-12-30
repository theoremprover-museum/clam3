/*  Based on Code by Ian for clam2.4 */

/*
 * The predicate wat(Term) holds if Term denotes a well-annotated term.
 *
 */

wat(Term):- 
    wat(Term, outwave),!.

/*
 * wat/2 uses the status flag inwave/outwave to keep
 * track of wave-front nestings.
 *
 */

wat(Var, _):- 
    var(Var),!.
wat('@wave_var@'(Term), Status):- !,
    Status = inwave,
    wat(Term, outwave).
wat('@wave_front@'(_, _, Term), Status):- !,
    Status = outwave,
    wat(Term, inwave).
wat(Term, _):- 
    atom(Term).
wat(Term, Status):-
    Term =.. [_F|Args],
    wats(Args, Status).

wats([], _).
wats([H|T], Status):-
    wat(H, Status),
    wats(T, Status).

/*
 * wave_terms_at/3 
 *
 * Take a goal of the form X = Y in Type, where the wave-fronts in X
 * are beached, then this predicate never takes X as a possible 
 * candidate for rippling

 * LD.  I've added extra literals to prevent wave_terms_at considering
 * the whole expression as opposed to just Term.


 */
wave_terms_at(Exp,Pos,SubExp):-
	               matrix(_, Term in _, Exp),
		       contains_wave_fronts(Term),
		       exp_at(Term, Pos2, SubExp),
		       \+ atomic(SubExp),
                       contains_wave_fronts(SubExp),
                       wat(SubExp),
		       exp_at(Exp, Pos1, Term),
		       append(Pos2, Pos1, Pos),
                       exp_at(Exp,Pos,SubExp).

/* LD.  Not used because doesn't allow term to contain annotations.
 * ann_exp_at(+TopLevel,?Flag,+Exp,?Pos,?SubExp).
 * much the same as exp_at/3;
 * Flag and TopLevel are tokens from the set {in_front,in_hole}.
 * TopLevel indicates whether Exp (a term) is a wave-front or a
 * wave-hole.  Normally, this is "in_hole" since that corresponds to
 * well-annotated terms;  occasionally, it is necessary to pass 
 * the contents of a wave-front to ann_exp_at (ie a term in which the
 * uppermost annotation (if any) is a wave-hole, not a wave-front); in
 * this case TopLevel should be set to "in_front".
 * 
 * Flag indicates the state of SubExp within Exp, whether it is in a
 * front or a hole; for example to generate possible terms for
 * rippling (i.e., terms which are well-annotated) use:
 * 
 * ann_exp_at(in_hole, in_hole, Exp, Pos, SubExp)
 * 
 * in this way, you are assured (*) that SubExp is a well-annoted
 * term, suitable for rippling.
 * 
 * NOTE(*).  All this comment (and the code too) assumes that (modulo
 * the setting of TopLevel) Exp is a Well-Annotated Term. 
 *
 * ann_exp_at/3 is a convenient wrapper.
 */
/* ann_exp_at(Exp,Pos,SubExp) :-
    ann_exp_at(in_hole,in_hole,Exp,Pos,SubExp).
ann_exp_at(Flag, Flag, Var,[],Var) :- var(Var),!.
ann_exp_at(in_front, in_hole, '@wave_var@'(Exp),[],Exp).
ann_exp_at(in_hole, in_hole, '@wave_var@'(Exp),[],Exp) :-
    !,clam_error('term is not well annotated1').
ann_exp_at(in_hole, in_hole, '@sink@'(Exp),[],Exp).
ann_exp_at(in_front, in_hole, '@sink@'(Exp),[],Exp) :-
    !,clam_error('term is not well annotated2').
ann_exp_at(Flag, Flag, Exp,[],Exp) :- 
    \+ (functorp(Exp,'@wave_var@',1) v functorp(Exp,'@sink@',1)).
ann_exp_at(Current, Flag, Exp,[N|P],SubExp) :-
    ann_exp_at(Current, Flag, Exp,[N|P],SubExp,_).

ann_exp_at(_Current, _Flag, _,[],_,_) :- fail.
ann_exp_at(Current, Flag, Exp, Pos, SubExp, SupSubExp) :-
    numbervars(Pos,0,0),!,
    reverse(Pos,RPos),
    r_ann_exp_at(Current, Flag, Exp,RPos,SubExp,SupSubExp).
ann_exp_at(Current, Flag, Exp, Pos, SubExp, SupSubExp) :- 
    r_ann_exp_at(Current, Flag, Exp, RPos, SubExp, SupSubExp),
    reverse(RPos, Pos).

r_ann_exp_at(_Current, _Flag, Exp,_,_,_) :- var(Exp),!,fail.
r_ann_exp_at(_Current, _Flag, Exp,_,_,_) :- atomic(Exp), !, fail.

r_ann_exp_at(in_front, Flag, '@wave_var@'(Exp),[N],SubExp,SupExp) :- 
    r_ann_exp_at(in_hole, Flag, Exp,[N],SubExp,SupExp).
r_ann_exp_at(in_hole, _Flag, '@wave_var@'(_Exp),[_N],_SubExp,_SupExp) :- 
    !,clam_error('term is not well-annotated3').

r_ann_exp_at(Current,Flag, '@sink@'(Exp),[N],SubExp,SupExp) :- 
    r_ann_exp_at(Current,Flag, Exp,[N],SubExp,SupExp).

r_ann_exp_at(in_hole,Flag,'@wave_front@'(Typ,Dir,Exp),[N],
	     SubExp,'@wave_front@'(Typ,Dir,Exp)) :- 
    r_ann_exp_at(in_front,Flag,Exp,[N],SubExp,Exp).
r_ann_exp_at(in_front,_Flag,'@wave_front@'(_Typ,_Dir,_Exp),[_N],
	     _SubExp,'@wave_front@'(_Typ,_Dir,_Exp)) :- 
    !,clam_error('term is not well-annotated5').
r_ann_exp_at(in_front,in_hole,SupExp, [N], Exp, SupExp) :-
    \+ functorp(SupExp,'@wave_front@',3),
    \+ functorp(SupExp,'@wave_var@',1),
    \+ functorp(SupExp,'@sink@',1),
    genarg0(N,SupExp,Exp1), N > 0,		%[0] is in a front too
    (functorp(Exp1,'@wave_var@',1)->Exp1='@wave_var@'(Exp)).
*/
/* check for a wave-front just below here */
/*
r_ann_exp_at(in_hole,in_front,SupExp, [N], Exp, SupExp) :-
    \+ functorp(SupExp,'@wave_front@',3),
    \+ functorp(SupExp,'@wave_var@',1),
    \+ functorp(SupExp,'@sink@',1),
    genarg0(N,SupExp,Exp1), N > 0,		% looking for an argument
    functorp(Exp1,'@wave_front@',3),
    Exp1='@wave_front@'(_,_,Exp).

r_ann_exp_at(in_hole,in_hole,SupExp, [N], Exp, SupExp) :-
    \+ functorp(SupExp,'@wave_front@',3),
    \+ functorp(SupExp,'@wave_var@',1),
    \+ functorp(SupExp,'@sink@',1),
    genarg0(N,SupExp,Exp1), 
    (functorp(Exp1,'@sink@',1)->Exp1='@sink@'(Exp);
     (functorp(Exp1,'@wave_var@',1)->clam_error('term is ill-annotated6');
      Exp1=Exp)).

r_ann_exp_at(in_front,in_front,SupExp, [N], Exp, SupExp) :-
    \+ functorp(SupExp,'@wave_front@',3),
    \+ functorp(SupExp,'@wave_var@',1),
    \+ functorp(SupExp,'@sink@',1),
    genarg0(N,SupExp,Exp1),
    (\+functorp(Exp1,'@wave_var@',1)->Exp1=Exp).

r_ann_exp_at(in_front,Flag,'@wave_var@'(Exp),[N1,N2|Ns], SubExp,
	     SupExp) :- !,
    r_ann_exp_at(in_hole,Flag,Exp,[N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(Current,_Flag,'@wave_var@'(_Exp),[_N1,_N2|_Ns], _SubExp, _SupExp) :- 
    \+var(Current),
    clam_error('term is not well-annotated!7').

r_ann_exp_at(in_hole,Flag,'@sink@'(Exp),[N1,N2|Ns], SubExp, SupExp) :- !,
    r_ann_exp_at(in_hole,Flag,Exp,[N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(in_front,_Flag,'@sink@'(_Exp),[_N1,_N2|_Ns], _SubExp, _SupExp) :- !,
    clam_error('term is not well-annotated!8').

r_ann_exp_at(in_hole,Flag,'@wave_front@'(_,_,Exp),[N1,N2|Ns], SubExp, SupExp) :- 
!,
    r_ann_exp_at(in_front, Flag, Exp, [N1,N2|Ns], SubExp, SupExp).

r_ann_exp_at(Current, Flag, Exp, [N1,N2|Ns], SubExp, SupExp) :-
    genarg0(N1,Exp,Arg),
    r_ann_exp_at(Current, Flag, Arg, [N2|Ns], SubExp, SupExp).
*/
contains_wave_fronts(Term) :-
    wave_fronts(_,[_|_],Term),!.

















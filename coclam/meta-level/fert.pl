/****************************************************************************

   File:fert.pl
   Author:Louise Dennis
   Last Modified: 27th August 1997

   Extenstions to instantiate/3 to allow for higher order matching and
   the presence of appn
****************************************************************************/

/* Modified Sept 10th, added comments */

fert:- consult('~/xclam/fert.pl').

% NB. instantiate changed to my_instantiate (louised)
% ind_hyp_match/4
%
% First-order case
%
ind_hyp_match(Var, H, G, []):-
    not potential_wave_occ(G),
    % matrix(_, L = R in _, G),
    matrix(_, M, G),
    induction_hyp(Var: IndHyp, H),
    my_instantiate(IndHyp, M, _).
%
% Higher-order case
%
ind_hyp_match(Var, H, G, SubstL):-
    matrix(Vars, M, G),
    potential_wave_occ(M),
    % (fully_rippled(M); 
    % not definite_wave_occ(M),
    coerce_meta_variables(M, SubstL1),
    wave_fronts(ErasedM1, _, M),
    apply_subst_list(SubstL1, ErasedM1, ErasedM2),
    append(H, Vars, Context),
    coerce_sinks(Context, ErasedM2, SubstL2),
    apply_subst_list(SubstL2, ErasedM2, ErasedM3),
    apply_subst_list(SubstL2, H, NewH),
    matrix(Vars, ErasedM3, NewG),
    \+ disprove(NewH==>NewG),
    induction_hyp(Var: IndHyp, H),
    my_instantiate(IndHyp, ErasedM3, _),
    append(SubstL1, SubstL2, SubstL).
%
% Forcing fertilization projection of
% meta wave-functions.
%
ind_hyp_match(Var, H, G, SubstList):-
    matrix(Vars, L = R in Typ, G),
    potential_wave_func(L),
    potential_wave_func(R),
    strip_meta_annotations(L, EraseL),
    strip_meta_annotations(R, EraseR),
    meta_term_occ_at(EraseL, PosL, MTermL),
    meta_term_occ_at(EraseR, PosR, MTermR),
    build_projection(MTermL, SubstL),
    build_projection(MTermR, SubstR),
    append(SubstL, SubstR, SubstList),
    apply_subst_list(SubstList, EraseL = EraseR in Typ, NewM),
    matrix(Vars, NewM, NewG),
    apply_subst_list(SubstList, H, NewH),
    \+ disprove(NewH==>NewG),
    induction_hyp(Var: IndHyp, H),
    apply_subst_list(SubstList, IndHyp, NIndHyp),
    my_instantiate(NIndHyp, NewM, _),
    writef('%t==>%t\n',[NewH,NewG]).


%% My additions (louised) - instantiate extended to cope with matching
%% terms involving appn e.g. matching s(X) to appn(N, s, X).

my_instantiate(A, B, C):-
	instantiate(A, B, C).
my_instantiate(CoIndHyp, Matrix, _):-
	matrix_conds(_, CA, related(A, B), Type, Matrix),
	strip_meta_annotations(related(A, B), related(AUnAnn, BUnAnn)),
	matrix_conds(Vs, CB, related(A1, B1), Type, CoIndHyp),
	matrix(Vs, CB, CH),
	instantiate(CH, CA, _),
	   %% any conditions for the hyp and conclusions match
	replace_ho_universal_vars(Vs, related(A1, B1), related(LA1, LB1), _),
	   %% Lift the Hypothesis 
	check_appn(AUnAnn, LA1),
	check_appn(BUnAnn, LB1).  %% match each side of the relation
	                          %% filtering uniformly for occurences of appn

%% A = B				  
check_appn(A, B):- var(B), A=B, !.   
check_appn(A, B):- atomic(A), A=B, !.
%% A = appn(0, function, B)
check_appn(A, appn(0, _, B)):- A=B, !.
%% A and B have same outermost function - recurse through arguments
check_appn(A, B):- \+ atomic(A), \+ var(B),
	A =.. [F|Args],
	B =.. [F|BArgs],!,
	check_appn_list(Args, BArgs).
%% A = F(X) and B = F of Y recurse through argurments
check_appn(A, B):- \+ atomic(A), \+ var(B),
	A =.. [F|Args],
	B =.. [of|[F|BArgs]],!,
	check_appn_list(Args, BArgs).
%% A = F(F'(X)) and B = appn(s(N), F(F'), Y) recurse on X appn(N, F, Y)
%% This is not as general as it might be.
check_appn(X, appn(s(N), F1, B)):-  \+ var(X),
	X =.. [F|[E]],
	\+ var(F),
	\+ F = appn,
	F1 =.. [F|[F2]], %% F1 is a compound function for nat3 needs
			 %% to be generalized. 
	E =.. [F2|XArgs],
	reverse(XArgs, [B2|B3]),
	reverse(B3, B5),!,
	check_appn(B2, appn(N, F1, B)).
%% A = F(X) and B = appn(s(N), F, Y) recurse on X appn(N, F, Y)
check_appn(X, appn(s(N), F1, B)):-  \+ var(X),
	X =.. [F|XArgs],
	\+ var(F),
	\+ F = appn,
	F1 =.. [F|B5],
	reverse(XArgs, [B2|B3]),
	reverse(B3, B5),!,
	check_appn(B2, appn(N, F1, B)).
%%  A matches B, but not without further work.
check_appn(A, appn(0, _, B)):- \+ atomic(A), !,
	check_appn(A, B).

%% Case to recurse through function arguments.
check_appn_list([], []).
check_appn_list([H|T], [H1|T1]):-
	check_appn(H, H1),
	check_appn_list(T, T1).
	

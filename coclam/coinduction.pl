/*****************************************************************************
      File: coinduction.pl

      Author: Louise Dennis

      Last Modified: 11th August 1997

      Description:  Prolog Code for the coinduction method.
        See ~louised/coinduction/clam/spec(.tex/.dvi) for full description

        To be included with induction
  
      Predicates: inT/2, form_set/4

*****************************************************************************/

 %% DESCRIPTION OF COINDUCTION PROOF METHOD FROM BBNOTE (sink.tex)
 %%
 %% Pre-Conditions
 %%
 %% 1. The current goal is of the form ALL x1:t1, ... xN:tN. a(x):t
 %% 2. t is know to be the greatest fixpoint of the function F
 %%
 %% New Goal
 %%
 %% range(%x.a(x)) <= F(range(%x.a(x))) U gfp(F)

 %% In practice there are two major classes of coinductive proof which
 %% can generally be descibed as "type-membership" and "equivalence"
 %% generally the code that follows will treat them separately.

/**************************************************************************/
 %% 1st Pre-Condition


 %% inT(+Goal, -Set)
 %%
 %% Takes the current goal and checks to see if it is either a
 %% set-membership goal or a goal that might lead to an observational
 %% equivalence proof.

 inT(Goal, Type):-
	matrix(_, G, Goal),
	tych(G, Type).
 inT(Goal, Type-eq):-
	matrix(_, G, Goal),
	tycheq(G, Type).

 tych(A in Type, Type):-
	\+ A = sim(_,_),
	\+ A = (_=_),
        \+ A = related(_, _),
	\+ A =.. [and|_].
 tych(_=>B, Type):-
	tych(B, Type).

%% tycheq(equiv(_,_) in Type, Type).
tycheq(sim(_,_) in Type, Type).
tycheq(_=>B, Type):-
	tycheq(B, Type).

/**************************************************************************/
 %% 2nd Pre-Condition
 %% See lang.pl

/**************************************************************************/
 %% New Goal


 %% form_set(+Hypotheses, +Goal, +Function, -NewGoalList)
 %% Forms a set, S, from the Goal using the rule-of-thumb heuristic
 %% and forms a new goal range(%x.a(x)) <= F(range(%x.a(x))) U gfp(F)
 %%
 %% In what follow the "U gfp(F)" is ignored for readability and
 %% simplicity reasons.  It is assumed to be present however.

form_set(Vs, union([range(Type-LTerm)]), Term, F, NewGoal, Type):-
	\+ ground(LTerm),
	form_lambda_term(Vs, Term, LTerm, Type),
	form_set_or_bisim(union([range(Type-LTerm)]), F, NewGoal).
        % Note that we have the wrong type for the term here -
	% temporary measure while I think about other things.

form_set(_, R, _, F, NewGoal, _):-
	ground(R),
	form_set_or_bisim(R, F, NewGoal).

%% form_lambda_term([], equiv(A, B), related(A, B)):-!.
 form_lambda_term([], sim(A,B), related(A, B), _):-!.
 form_lambda_term([], Term, related(Term, type(Term, Type)), Type).
 form_lambda_term([H:Type|T], Term, lam(H-Type, NewTerm), Ty):-
	form_lambda_term(T, Term, NewTerm, Ty).

 form_set_or_bisim(LTerm, F of X, subset(LTerm, F of [X, LTerm])):-!.
 form_set_or_bisim(LTerm, F, subset(LTerm, F of LTerm)).
	

%% UTILITIES.  sort_conds for rationalising goals with explicit
%%  conditions, typ/2 for finding the Type from some of the structures.
 sort_conds(Term in Type, [], Type, Term):-!.
 sort_conds(A=>B, [A|Conds], Type, Term):-
	sort_conds(B, Conds, Type, Term).

 typ(Type-eq, Type).
 typ(Type, Type):-
	\+ Type = _-eq.

append_conds([], [], []).
append_conds([], [V:T|R], [T|OutR]):-
	append_conds([], R, OutR).
append_conds([H|T], L, [H|Out]):-
	append_conds(T, L, Out).






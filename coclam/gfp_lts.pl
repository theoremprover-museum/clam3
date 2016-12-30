/*****************************************************************************
      File: gfp.pl

      Author: Louise Dennis

      Last Modified: 15th August 1997

      Description:  Prolog Code for the first gfp_membership method
        See ~louised/coinduction/clam/spec(.tex/.dvi) for full description
  
      Predicates: 
*****************************************************************************/


 %% DESCRIPTION OF BISIMULATION PROOF METHOD FROM BBNOTE  (sink.tex)
 %%
 %% Pre-Conditions
 %%
 %% 1. There is a goal of the form
 %% range(%x.a1(x)) U ... U range(%x.aN(x)) <=
 %%                           F(range(%x.a1(x)) U ... U range(%x.aN(x)))
 %% 2. By definition F(S) = {f(x): x in S}
 %% 3. For each i, xi has been chosen as a suitable coinduction variable or
 %% generator for ai, with g(yi) as a coinduction term with which it
 %% will be replaced in the coinduction conclusion.  In the case of
 %% relations, two coinduction terms will be chosen, one for each side
 %% of the relation.
 %%
 %% New Goals
 %%
 %% 1. For each i.
 %% ALL x. a1(x) in S & ... & aN(x) in S ->
 %%                   ALL x. f(-1)(ai(g(yi))) in S.
 %% With wavefronts provided by difference matching and sinks around
 %% all the variables.
 %% 2. Various proof obligations, depending on ${\cal F}$ (usually to
 %% do with heads of lists) and often with rewriting using the same
 %% annotations as for goal 1.
 %% 3. Various ``base case'' obligations, if applicable.

 
/**************************************************************************/
 %% Pre-Condition 1
 

 %% subset_goal(+Goal, -Set, -Function, -Type)
 %% Checks that the goal is of the appropriate form (i.e. S  <  F(S)).

 subset_goal(G, Conds, S, F, Type):-
	matrix([], Term, G),
	sort_conds(Term, Conds, set(Type), subset(S, F of S)),
	\+ S = [_|_].
 subset_goal(G, Conds, S, F of X, Type):-
	matrix([], Term, G),
	sort_conds(Term, Conds, set(Type), subset(S, F of [X, S])).


/**************************************************************************/
 
 %% set_to_function(+/-Vs, -/+Lambdafunction, +/-setdescription)
 %% Takes a set description (e.g. S = {lconst(a):a.tau}) and list of
 %% variables with types and turns it into a lambda function (%a.tau
 %% lconst(a)) or vice versa.
 set_to_function([], Term, Term):-
	\+ Term = lam(_, _).
 set_to_function([H:Type|Tail], lam(H-Type, LTerm), Term):-
	set_to_function(Tail, LTerm, Term).	


/***************************************************************************/
%% Post-Conditions
%%
%% Forms goal(s) x in S => tl(x) in S.  The (in S) has been left out, because 
%% I'm lazy and can't be bothered to change all the represenations.

%% gfp_proof_goals(+Set, +F, +Type, -Goals)
gfp_proof_goals(H, Set, F, Type, Goals, Conds):-
	recurse_union_gfpa(Set, F, Type, Hyps, Concs, Conds),
	append(H, Hyps, Hs),
	form_goals_gfpa(Hs, Concs, Goals).

form_goals_gfpa(_, [], []).
form_goals_gfpa(Hyps, [Conc|Concs], [Hyps==>Conc|Goals]):-
	form_goals_gfpa(Hyps, Concs, Goals).

%% recurse_union_gfpa(+Set, +Function, +Type, -Hypotheses, -Conclusions)
%% Recurses down the set, forming appropriate Hypotheses and Conclusions

recurse_union_gfpa(union([]),_,_,[],[],_).
recurse_union_gfpa(union([range(Typ-LTerm, SConds)|T]), F, Type,
		   [RAW:ih(Hyp)|Hyps], [ConcC|ConcList], TConds):-
	set_to_function(Vars, LTerm, Term),
        append_conds(SConds, TConds, Conds),
	matrix_conds(Vars, Conds, Term, Typ, Hyp),
	conclusion(Vars, Term, F, Typ, Conc),
	matrix(ConcVars, ConcT, Conc),
	append_relevant(ConcVars, Conds, ConcT, ConcT1),
	matrix(ConcVars, ConcT1, ConcC),
	recurse_union_gfpa(union(T), F, Type, Hyps, ConcList, TConds).

append_relevant(_, [], C, C).
append_relevant(Vars, [Cond|Conds], Tm, Cond=>Out):-
	member(V:T, Vars),
	exp_at(Cond, _, V), !,
	append_relevant(Vars, Conds, Tm, Out).
append_relevant(Vars, [Cond|Conds], Tm, Out):-
	append_relevant(Vars, Conds, Tm, Out).

	
%% conclusion(+Vars, +Term, +F, +Type, -ConclusionList)
%% Forms conclusions for each inverse of F.

conclusion(Vars, Term, _, Type, Conc):-
	\+ Term = related(_,_),
	matrix(Vars, act(Term) in Type, Conc).
conclusion(Vars, related(A, B), _, Type, Conc):-
	matrix(Vars, and(act(A), act(B)) in Type, Conc).

	







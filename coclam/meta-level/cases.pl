/*****************************************************************************
      File: cases.pl

      Author: Louise Dennis

      Last Modified: Wednesday 26th February

      Description: Modified Prolog Code for casesplit critic.
  
      Predicates: split_into_nonripple_cases/4

*****************************************************************************/

%% split_into_nonripple_cases/4 is similar to the predicate appearing
%% in Andrew's clam.v3.2 code except that G not M is passed to
%% exp_at.  This is because of modifications in the wave
%% preconditions.  Secondly Pos has been changed to Exp in the call to
%% replace, since I couldn't see how it was expected to work otherwise.
%%
%% This code is still buggy Pos doesn't relate to the G passed to it !!!
%%
%% In general split_into_nonripple_cases generates new hypotheses
%% relating to any potential case splits and strips of all meta
%% annotations.  (split_into_ripple_cases) deals with case splits
%% involving wave rules.
%%
%% This is another reason to suppose that this is not the heart of the
%% problem, since it should be wave rules that the lconstlswap example
%% that causes this problem is calling.
split_into_nonripple_cases([], _, _, []).
split_into_nonripple_cases([Cond|Conds], Pos, H==>G, [NH==>NG|Sequents]):-
        matrix(Vs, M, G),
	extend_hyps_with_cond(Cond, Vs, H, NH),
	exp_at(G, Pos, Exp),
        strip_meta_annotations(Exp, NExp),
        replace(Pos, NExp, M, NM),
        matrix(Vs, NM, NG),
        split_into_nonripple_cases(Conds, Pos, H==>G, Sequents).

replace_vars_in_goal(G, Var, Term, NewG):-
        replace_all(Var, Term, G, NewG).


construct_case_goals(H, G, Cases, Pos, SubGs):-
	matrix(Vars, Matrix, G),
	exp_at(G, Pos, Sexp),
	exp_at(Matrix, NewPos, Sexp),
	listof(Var:Typ, (member(Var:Typ,Vars),
                         not freevarincondition(Cases,Var)),
               NewVars1),
        listof(Var:Typ, (member(Var:Typ,Vars),
                         freevarincondition(Cases, Var)),
               NewVars2),
        matrix(NewVars1, Matrix, NewMatrix),
        append(NewVars2, H, NewH),
        split_into_cases(Cases, NewPos, NewH==>NewMatrix, SubGs).









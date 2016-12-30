/*****************************************************************************
        File: intro.pl
        Author: Louise Dennis

Predicates for the introduce_constructor method.
******************************************************************************/

/* Modified September 1st - det goal checks type of hypothesis */

%% eval_bf
%% eval_bf([], [norules], [], _).
%%eval_bf(_, _, _, 40, _,_,_,_,_):-   %% Purely arbitrary cut off for
                                      %% terms with no WHNF
%%	!,
%%	fail.

%%  Immediate Transitions
eval_bf([_-r(R, P, _, Vs)|_], Rules, Cout, _, G, H1, R1, Cout, _):-
%%	n_strict(H, H1, R1, P, C, Cout),
%%      evaluation now occurs before the call to eval_bf to speed things up.
	\+ member(_:X=X in _ => void, Cout),   %% for lswaplconst
	transition(Conds, H1,_,_),
	check_tran_conds(Conds, Cout, G, H1, Vs),
	append(R, R1, Rules), !.

%%  
eval_bf([_-r(R, P, _, Vs)|T], OutR, OutC, N, G, H1, R1, COut, AllVs):-
	transition(Conds, H1,_,_),

	%% Checking for consistency of the conditions - i.e. that they
	%% only impose typing conditions or conditions already assumed.
	\+ (member(A:TYpe, Conds), member(A:NTYpe, Vs), \+TYpe=NTYpe),

	%% There is an "interesting" condition before a transitions
	%% will apply
	member(X, Conds), \+ member(_:X, COut),
	\+ X = (_:_),
	\+ X = (H1 in _),

	consistent(Vs, [Num:X|COut]),
	make_ground([[Num:X|COut], AllVs]),
	append(R, R1, R2),

	%% Assume condition and continue
        append(T, [H1-r(R2, P, [Num:X|COut], Vs)], [HN-r(RN, PN, CN,
	VsN)|NewStack]), 
	%% ? changed R2 from R1 
	N1 is N + 1,
	n_strict(HN, NH1, NR1, PN, CN, NCOut),
	eval_bf([HN-r(RN, PN, CN, VsN)|NewStack], OutR, OutC, N1, G, NH1, NR1, NCOut, AllVs).

%% Case split variables and continue
eval_bf([_-r(R, P, _, Vs)|T], OutR, OutC, N, G, H1, R1, COut, AllVs):-
	\+ member(_:X=X in _ => void, COut),   %% for lswaplconst
	matrix(_, Term, G),
	sort_conds(Term, _, Type, _),

	%% any conditions are trivial
	(\+ transition(_, H1,_,_);
	(transition(Conds, H1,_,_), 
	member(X, Conds), \+ member(_:X, COut),
	\+ X = (_:Type), \+ X = (H1 in Type))),

	
	append_splits(R, R1, R2),
        case_split(Vs, H1, R2, P, COut, Terms, [], AllVs), \+ Terms=[],
        append(T, Terms, [HN-r(RN, PN, CN, VsN)|NewStack]),
	N1 is N + 1,
	n_strict(HN, NH1, NR1, PN, CN, NCOut),
	eval_bf([HN-r(RN, PN, CN, VsN)|NewStack], OutR, OutC, N1, G, NH1, NR1, NCOut, AllVs).

%% Append together rules, but where rule splitting a variable appears
%%	twice  instead introduce a rule that the variable be split twice.
append_splits([], P, P).
append_splits([split-Vs-N|Splits], M, [split-Vs-N|Out]):-
	\+member(split-Vs-_, M),
	append_splits(Splits, M, Out).
append_splits([Rule|Splits], M, [Rule|Out]):-
	\+ Rule = split-_-_,
	append_splits(Splits, M, Out).
append_splits([split-Vs-N|Splits], M, Out):-
	nth(Num, M, split-Vs-N1, Rest),
	N2 is N1 + 1,
	nth(Num, NewM, split-Vs-N2, Rest),
	append_splits(Splits, NewM, Out).
        

%% non_strict evaluation of ground term without any case splitting
n_strict(A, B, C, D, E, F):-
	non_strict(A, B, C, D, E, F, 0).
n_strict(A, A, [], _, E, E).


%%%non_strict(Term, Term, [], _, C, C):- atomic(Term), !.
non_strict(Term, NT, Rules, P, Cin, Cout, N):-
        \+ var(NT),
        Term =..[TermFunctor|TermArgs],
        NT =..[TermFunctor|DiffArgs], !,
	N1 is N + 1,
        non_strict(DiffArgs, TermArgs, Rules, P, 1, Cin, Cout, N1).
non_strict(Term, NT, RuleList, P, CSoFar, Conds, N):-
        skeleton(Term, VarTerm),
        Term =.. [TermFunctor|TermArgs],
        VarTerm =.. [TermFunctor|VarArgs], 
        function_defn(VarTerm, Rule:C=>VarTerm:=>NewTerm),
	numa(C, NumC),
        append(NumC, CSoFar, C1),
        consistent(_, C1),
	N1 is N + 1,
        non_strict(VarArgs, TermArgs, RuleL, P, 1, C1, C2, N1),
         consistent(_, C1),
	tidy_lam(NewTerm, NN),
        n_strict(NN, NT, RuleListB, P, C2, Conds),
        append(RuleL, [Rule-P|RuleListB], RuleList).

numa([], []).
numa([H|T], [_:H|NewT]):-
	numa(T, NewT).


non_strict(_, _, _, _, _, _, _, N):- N > 20, !, fail.
non_strict([], [], [], _, _, C, C, _).
non_strict([H|T], [H|A], Rules, P, N, Cin, Cout, M):-
        N1 is N + 1, !,
	M1 is M + 1,
        non_strict(T, A, Rules, P, N1, Cin, Cout, M1).
non_strict([H|T], [LamH|A], Rules, P, N, Cin, Cout, M):-
	tidy_lam(LamH, H),
        N1 is N + 1,!,
	M1 is M + 1,
        non_strict(T, A, Rules, P, N1, Cin, Cout, M1).
non_strict([A|T], [Blam|S], RuleList, P, N, Cin, Cout,M):-
        \+ A = Blam,
        \+ tidy_lam(Blam, A),
        tidy_lam(Blam, B),
        A=..[F|_],
        B=..[F1|_],
        \+ F = F1,!,
	M1 is M + 1,
        non_strict(B, A, RuleListA, [N|P], Cin, C1,M1),
        N1 is N + 1,
        non_strict(T, S, RuleListB, P, N1, C1, Cout, M1),
        append(RuleListA, RuleListB, RuleList).
non_strict([A|T], [Blam|S], RuleList, P, N, Cin, Cout, M):-
        \+A = Blam,
        \+ tidy_lam(Blam, A),
        tidy_lam(Blam, B),
        A=..[F|A1],
        B=..[F|A2], !,
	M1 is M + 1,
        non_strict(A1, A2, RuleListA, [N|P], 1, Cin, C1, M1),
        N1 is N + 1,
        non_strict(T, S, RuleListB, P, N1, C1, Cout, M1),
        append(RuleListA, RuleListB, RuleList).

%% Case split all variables once only.
%%

case_split([], _, _, _, _, [], _,_).
case_split([V:T|Vs], A, B, C, D, Out, E, AV):-
	setof(Var, Cases^(data(Var, T, Cases, rec); data(Var, T, Cases,
	non_rec)), Vars), 
	Vars = [V], !,
	case_split(Vs, A, B, C, D, Out, E, AV).
case_split([V:T|Vs], Term, Rule, Pos, Cond, [NT-r(R, Pos, Cond,
	                            NewVs)|Out], OVs, AV):- 
	data(NewVar, T, Cases, rec),
	replace_all(V, NewVar, Term, NT),
	make_ground([Vs, NT, Cases, AV]),
	append(Rule, [split-[V/NewVar]-1], R),
	append(Cases, Vs, NVs),
	append(NVs, OVs, NewVs),
	case_split(Vs, Term, Rule, Pos, Cond, Out, [V:T|OVs], AV).
case_split([V:T|Vs], Term, Rule, Pos, Cond, [NT-r(R, Pos, Cond,
	                            NewVs)|Out], OVs, AV):- 
	\+ data(_, T, _, rec),
	data(NewVar, T, Cases, non_rec),
	replace_all(V, NewVar, Term, NT),
	make_ground([Vs, NT, Cases, AV]),
	append(Rule, [split-[V/NewVar]-1], R),
	append(Cases, Vs, NVs),
	append(NVs, OVs, NewVs),
	case_split(Vs, Term, Rule, Pos, Cond, Out, [V:T|OVs], AV).
case_split([V:T|Vs], Term, Rule, Pos, Cond, Out, OVs, AV):-
	\+ data(_, T, _, rec), \+ data(_, T, _, non_rec),
	case_split(Vs, Term, Rule, Pos, Cond, Out, [V:T|OVs], AV).
	

case_are([], [], []).
case_are([split-[Var/Cas]-N|T], R, [Var/Cas-N|C]):- !,
	case_are(T, R, C).
case_are([Rule-Pos|T], [Rule-Pos|R], C):-
	case_are(T, R, C).


%% Applies trivial to a list of hyps
trivial_list(H==>C, D):-
    \+ var(C),
    trivial_list(H,C, D).
trivial_list(_,[], []).
trivial_list(H,[C|T], D):-
    strip_meta_annotations(C,CC),
    elementary(H==>[CC],_), !,
    trivial_list(H, T, D).
trivial_list(H,[C|T], [C|D]):-
    strip_meta_annotations(C,CC),
    noelementarystuff(H, CC), !,
    trivial_list(H, T, D).

noelementarystuff(H, CC):-
	\+ elementary(H==>[CC],_).
noelementarystuff(H, CC):-
	\+ CC = (_=>void),
	\+ elementary(H==>[CC=>void],_).
noelementarystuff(H, C=>void):- 
	\+ elmentary(H==>[C],_).

%% *********************POST CONDITIONS****************************

%%  intro_cons/5, the main predicate.  Applies a list of "rules" that
%%  apply to 
%%  a term within the goal.  This term is not annotated.
%%  intro_cons first increases the set of conditions then cases splits
%%  variables and findally applies rewrites.	

intro_cons([], H==>Goal, H==>Goal, G, [], [], []).
%%  Apply rewrite rule
intro_cons([Rule-Pos|Rules], H==>G, OutGoal, OldG, [], [], CaseGoals):-
	matrix_conds(Vs, TermConds, Term, Type, G),
	exp_at(Term, Pos, Sub),

	function_defn(Sub, Rule:Conds=>Sub:=>SubR),
	instan(Conds, H), !, 
	
	apply_rule(SubR, Term, NewTerm, Pos),
	matrix_conds(Vs, TermConds, NewTerm, Type, NewGoal),
	intro_cons(Rules, H==>NewGoal, OutGoal, OldG, [], [], CaseGoals).
%% Case Split
intro_cons(Rules, H==>G, OutGoal, OldG, [CaseVar|Cases], [],
	                                         OtherGoals):-  
	apply_cases(CaseVar, H==>G, BaseCase, RecCase, Cases, NewCases),
	intro_cons(Rules, RecCase, OutGoal, OldG, NewCases, [], CaseGoals),
	append(BaseCase, CaseGoals, OtherGoals).
%% Increase hypothesis set.
intro_cons(Rules, H==>G, OutGoal, OldG, Cases, [Condition|Conditions],
	                                         Out):-  
	apply_condition(Condition, H==>G, OtherCases, CondCase),
	make_ground([OtherCases, CondCase, H, G]),
	intro_cons(Rules, CondCase, OutGoal, OldG, Cases, Conditions,
	                                                       CaseGoals),
	append(OtherCases, CaseGoals, Out).

%%  Checks that conditions of the rule are met by the hypotheses
instan([], _).
instan([X|T], H):-
	member(_:X, H),
	instan(T, H).
instan([X|T], H):-
	elementary([]==>[_:X], _), !,
	instan(T, H).
instan([B=A in Type|T], H):-
	member(_:A=B in Type, H),
	instan(T, H).
instan([B=A in Type=>void|T], H):-
	member(_:A=B in Type=>void, H),
	instan(T, H).

%%  Finding variables in the Hypotheses
%%
find_Vs([], [], []).
find_Vs([Var:Type|T], [Var:Type|Tail], Rest):-
	data(Var, Type, _, _), !,
	find_Vs(T, Tail, Rest).
find_Vs(T, [Var:Type|Tail], [Var:Type|Rest]):-
	find_Vs(T, Tail, Rest).

%% Actually applies the chosen rule.
apply_rule(SubR, T, NewTerm, Pos):-
	replace(Pos, SubR, T, NT),
	tidy_lam(NT, NewTerm).

%% Performs appropriate case split.
%%
%% Data type with no base case and only one recursive case.
apply_cases(V/Rec-1, H==>G, [], RecH==>CaseR, CaseTrack, NewCaseTrack):-
	matrix(Vs, Phi, G),
	sort_conds(Phi, Conditions, Ty, Term),
	member(V:Type, Vs),
	\+ data(_, Type, _, non_rec),
	data(Rec, Type, DepsR, rec),
	make_ground([Vs, Rec, DepsR]),
	replace_all(V, Rec, Term, RecTerm),
	replace_all_l(V, Rec, Conditions, NewConditions),
	replace_all_l(V, Rec, CaseTrack, NewCaseTrack),
	nth(_, Vs, V:_, NewVs),
	replace_all_l(V, Rec, H, RecH),
	append(DepsR, NewVs, RVs),
	matrix_conds(RVs, NewConditions, RecTerm, Ty, CaseR).
apply_cases(V/_-0, H==>G, [], H==>G, C, C).
%%
%% Data type with two cases, one recursive
apply_cases(V/Rec-N, H==>G, [BaseH==>CaseB|Bases], OutH==>OutR, CT, NCT):-
	matrix(Vs, Phi, G),
	sort_conds(Phi, Conditions, Ty, Term),
	member(V:Type, Vs),
	data(Base, Type, DepsB, non_rec),
	make_ground([Vs, Base, DepsB]),
	data(Rec, Type, DepsR, rec),
	make_ground([Vs, Rec, DepsR]),
	replace_all(V, Base, Term, BaseTerm),
	replace_all_l(V, Base, Conditions, BaseConditions),
	replace_all(V, Rec, Term, RecTerm),
	replace_all_l(V, Rec, Conditions, RecConditions),
	replace_all_l(V, Rec, CT, NCTA),
	nth(_, Vs, V:_, NewVs),
	replace_all_l(V, Base, H, BaseH),
	replace_all_l(V, Rec, H, RecH),
	append(DepsB, NewVs, BVs),
	append(DepsR, NewVs, RVs),
	matrix_conds(BVs, BaseConditions, BaseTerm, Ty, CaseB),
	matrix_conds(RVs, RecConditions, RecTerm, Ty, CaseR),
	N1 is N - 1, 
	apply_cases(V/_-N1, RecH==>CaseR, Bases, OutH==>OutR, NCTA, NCT).
%% Data type with no recursive cases
apply_cases(V/_-1, H==>G, Bases, Rec, CT, CT):-
	matrix(Vs, Phi, G),
	sort_conds(Phi, Conditions, Ty, Term),
	member(V:Type, Vs),
	\+ data(_, Type, _, rec),
	set_of(Exp-Deps, data(Exp, Type, Deps, non_rec), Exps),
	make_ground([Vs, Exps]),
	nth(_, Vs, V:_, NewVs),
	setof(NH==>Case, Base^Dep^NVs^NTerm^NConds^(member(Base-Dep, Exps),
	              replace_all(V, Base, Term, NTerm),
		      replace_all_l(V, Base, Conditions, NConds),
	              replace_all(V, Base, H, NH),
		      append(Dep, NewVs, NVs),
		      matrix_conds(NVs, NConds, NTerm, Ty, Case)),
              [Rec|Bases]).  %% special case bool assumes only one
                               %% other case.

apply_condition(N:F=Y in Type, H==>G, OtherCases, [N:F=Y in Type|H]==>G):-
	setof(Rule, L^Hy^function_defn(F, Rule:Hy=>F:=>L), Rules),
	condlist(H==>G, Rules, OtherCases, N:F=Y in Type).
apply_condition(N:Cond, H==>G, [[N:Cond=>void|H]==>G], [N:Cond|H]==>G):-
	\+ Cond = (_=>void),
	\+ Cond = (F = Y).
apply_condition(N:Cond=>void, H==>G, [[N:Cond|H]==>G], [N:Cond=>void|H]==>G):-
	\+ Cond = (F = Y).


condlist(_==>_, [], [], _).
condlist(H==>G, [Rule|Rules], Out, N:F=Y in Type):-
	function_defn(F, Rule:_=>F:=>I),
	\+ mymatch(Y, I, _),
	find_Vs(Vs, H, Rest),
	replace_ho_universal_vars(Vs, Rest, RL, _),
	\+ consistent(Vs, [_:F=I in Type|RL]),
	condlist(H==>G, Rules, Out, N:F=Y in Type).
condlist(H==>G, [Rule|Rules], Out, N:F=Y in Type):-
	function_defn(F, Rule:_=>F:=>I),
	mymatch(Y, I, []),
	condlist(H==>G, Rules, Out, N:F=Y in Type).
condlist(H==>G, [Rule|Rules], Out, N:F=Y in Type):-
	function_defn(F, Rule:_=>F:=>I),
	sort_type([I:Type], Vars),
	mymatch(Y, I, List),
	make_ground([List, H, Vars, I]),
	\+ List = [],
	condlist2(H==>G, List, Vars, Out1, N:F=Y in Type, F=I in Type),
	condlist(H==>G, Rules, Out2, N:F=Y in Type),
	make_ground([Out1, Out2, G]),
	append(Out1, Out2, Out).
condlist(H==>G, [Rule|Rules], [NewHL==>G|Out], N:F=Y in Type):-
	function_defn(F, Rule:_=>F:=>I),
	\+ mymatch(Y, I, _),
	sort_type([I:Type], Vars),
	append(Vars, [_:F=I in Type|H], NewHL),
	make_ground(NewHL),
	condlist(H==>G, Rules, Out, N:F=Y in Type).

condlist2(_==>_, [], _, [], _, _).
condlist2(H==>G, [[Term, Var]|List], Vars, [[_:F=J in
                           Type|NewH]==>G|Out], N:F=Y in Type, F=I in Type):- 
	member(Var:Ty, Vars),
	data(L, Ty, _, K), \+ K = blip,
	L = Term,
	data(T, Ty, Deps, K1), \+ K1 = blip,
	\+ T = Term,
	replace_all(Var, T, I, J),
	append(Deps, H, NewH),
	condlist2(H==>G, List, Vars, Out, N:F=Y in Type, F=I in Type).
condlist2(H==>G, [[Term, Var]|List], Vars, Out, N:F=Y in Type, F=I in Type):- 
	member(Var:Ty, Vars),
	\+ (data(L, Ty, _, K), \+ K = blip, L = Term),
	condlist2(H==>G, List, Vars, Out, N:F=Y in Type, F=I in Type).
	
mymatch([], [], []):-!.
mymatch([A|AT],[B|BT], List):- !,
	mymatch(A, B, L1),
	mymatch(AT, BT, L2),  
	append(L1, L2, List).
mymatch(A, B, []):- atomic(B), A = B, !.
mymatch(A, B, [[A, B]]):-
	var(B), !.
mymatch(A, B, List):-
	\+var(B),
	B =.. [F|BArgs],
	A =.. [F|AArgs],!,
	mymatch(AArgs, BArgs, List).

mymatch([], [], [], _):-!.
mymatch([A|AT],[B|BT], List, Vs):- !,
	mymatch(A, B, L1, Vs),
	mymatch(AT, BT, L2, Vs),  
	append(L1, L2, List).
mymatch(A, B, [], _):- atomic(B), A = B, !.
mymatch(A, B, [[A, B]], Vs):- atomic(B), member(B:_, Vs), !.
mymatch(A, B, [[A, B]], _):-
	var(B), !.
mymatch(A, B, List, Vs):-
	\+var(B),
	B =.. [F|BArgs],
	A =.. [F|AArgs],!,
	mymatch(AArgs, BArgs, List, Vs).


replace_all_l(_, _, [], []).
replace_all_l(A, B, [H|T], [NewH|NewT]):-
	replace_all(A, B, H, NewH),
	replace_all_l(A, B, T, NewT).

%% det_goal/4.  Determines the new goal - only performs difference
%% matching if base cases are not involved, in fact the first two
%% goals are an attempt to "catch" base cases which are dealt with by
%% a disjunction in the goal - this is only a heurisitic based on
%% assuming that the rule applied will have reduced the term to nil or
%% 0 or whatever.
%%det_goal(_, related(A, B), _, BA = BB):- bt(A, B, BA, BB), !.
%%det_goal(_, A, _, AA):- \+ A =.. [and|_], bt(A, AA), !.
det_goal(H, Term, NewTerm, NewVs, AnnTerm, Type):-
	tidy_lam(NewTerm, NT),
	((member(_:ih(X), H),
	  matrix_conds(Vs, Conds, T1, Type, X),
	  tidy_lam(T1, related(A, B))
          ); tidy_lam(Term, related(A, B))),
	dm_vs(NT, related(A, B), AnnTerm, _, NewVs),
	!.


%% see_sinks/3  marks sinks if none are already marked.
see_sinks(_, DmTerm, DmTerm):-
	sinks(DmTerm, _).
see_sinks(NewVs, DmTerm, AnnTerm):-
	mark_sinks(NewVs, DmTerm, AnnTerm).
	
%% Determines if subterm has been reduced to a base case.
bt(A, Base):-
	A =.. [_, Base],
	base_type(_, Base).
bt(A, B, Base, BBase):-
	A =.. [Inv, Base],
	B =.. [Inv, BBase],
	(base_type(_, Base); base_type(_, BBase)).


%% Sorts out case splitting.
other_goals([], []).
other_goals([triv|List], NewList):-
	other_goals(List, NewList).
other_goals([[]|List], NewList):-
	other_goals(List, NewList).
other_goals([H|T], [H|List]):-
	\+ H = triv,
	other_goals(T, List).
	

reduce_d(E, Rule:C=>E:=>R, P, T):-
 	        function_defn(E, Rule:C=>E:=>R, P, T).
reduce_d(E, Rule:C=>E:=>R, _, _):-
	        copy_term(E, EC),
		pick_a_rule(Rule, C=>_:=>ECG, _, Vs),
		\+ function_defn(EC, Rule:C=>EC:=>_),
		\+ current_node(Rule, _),
		replace_universal_vars(Vs, ECG, ECGL, _),
		ECGL = EC,
	        is_a_reduction_rule(Rule, E, C=>E:=>R).

is_a_reduction_rule(Rule, E, C=>E:=>R):-
	is_a_reduction_rule(Rule, E, C=>E:=>R, _), !.

consistent(_, []).
consistent(Vs, [V:H|List]):- ground(H),
	\+ [H] = [_=>void], !,
	\+ member_var(V:H=>void, List), 
	\+ f(Vs, H, List),
	consistent(Vs, List).
consistent(Vs, [H|List]):-
	\+ [H] = [_=>void],
	\+ member_var(H=>void, List),
	\+ f(Vs, H, List),
	consistent(Vs, List).
consistent(Vs, [H=>void|List]):-
	\+ member_var(H, List),
	consistent(Vs, List).

f(Vs, A=B in _, List):-
	member(_:A=C in _, List),
	\+ mymatch(C,B,_, Vs).
f(Vs, _:A=B in _, List):-
	member(_:A=C in _, List),
	\+ mymatch(C,B,_, Vs).

member_var(A=A, _):- !, fail.
member_var(H, [H1|_]):-
	H = H1.
member_var(H, [H1|T]):-
	\+ H == H1,
	member_var(H, T).


%%% !!!!!!!!!  Make sure there will be no name-capture problems!!!!!!!!!!!
replace_ho_universal_vars(Vars, Term, NewTerm, Meta_types):-
    untype(Vars,Vs,Types), zip(VsNewVs,Vs,Metas),
    zip(Meta_types, Metas, Types), 
    replace_ho_universal_vars_1(VsNewVs,Term,NewTerm).
	
replace_ho_universal_vars_1(_,Tm,Tm) :- var(Tm),!.
replace_ho_universal_vars_1(VsNewVs,[H|T],[HH|TT]) :- !,
    replace_ho_universal_vars_1(VsNewVs,H,HH),
    replace_ho_universal_vars_1(VsNewVs,T,TT).
replace_ho_universal_vars_1([],In,In).
replace_ho_universal_vars_1([Object-Meta|Vars],In,Out) :- !,
    replace_ho_all(Object,Meta,In,Out1),
    replace_ho_universal_vars_1(Vars,Out1,Out).

replace_ho_all(_, _, Object1, Object1):-var(Object1),!.
replace_ho_all(Object, Meta, Object, Meta).
replace_ho_all(Object, _, Object1, Object1):-
	atomic(Object1),
	\+ Object = Object1, !.
replace_ho_all(Object, Meta, Object1, Meta1):-
	\+ atomic(Object1),
	Object1 =.. [Function|Args],
	\+ Function = Object, !,
	replace_ho_all_list(Object, Meta, Args, NewArgs),
	Meta1 =.. [Function|NewArgs].
replace_ho_all(Object, Meta, Object1, Meta1):-
	\+ atomic(Object1),
	Object1 =.. [Function|Args],
	Function = Object, !,
	replace_ho_all_list(Object, Meta, Args, NewArgs),
	Meta1 =.. [of|[Meta|NewArgs]].
replace_ho_all_list(_, _, [], []).
replace_ho_all_list(Object, Meta, [H|T], [NewH|NewT]):-
	replace_ho_all(Object, Meta, H, NewH),
	replace_ho_all_list(Object, Meta, T, NewT).
	
	
	
matrix_conds(Vs, Conds, Term, Type, G):-
	ground(Term),
	sort_conds(Temp, Conds, Type, Term),
        matrix(Vs, Temp, G), !.
matrix_conds(Vs, Conds, Term, Type, G):-
        matrix(Vs, Temp, G),
	sort_conds(Temp, Conds, Type, Term).








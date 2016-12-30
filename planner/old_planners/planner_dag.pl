/***********************************************************************
       
      This file contains code for the depth-first proof planner
      used by the critics version of CLaM (version 3.0) which
      has been extended to support the explicit constrcution
      of a goal tree.

 ***********************************************************************/

:- dynamic current_node/2.
:- dynamic open_nodes/2.
:- dynamic node/8.
:- dynamic planning_failure/2.
:- dynamic planner/1.

/*****************************************************************

 PLANNERS:


 *****************************************************************/

    % plan/0
    %
    %
plan:-
    current_goaltree(Name),
    current_node(Name, Addr),!,
    plan(Name, dplan).
plan:-
    writef('ERROR: No current goaltree\n').

    % plan/1
    %
    %
plan(Name):-
    plan(Name, Name, dplan),
    report_on_planning(Name).

    % plan/2
    %
    %
plan(Name, Planner):-
    plan(Name, Name, Planner).
plan(Name, _):-
    writef('Planning failed for %t\n',[Name]),fail.

    % plan/3
    %
    %
plan(RootName, Name, Planner):-
    current_node(Name, Addr),!,
    delete_branch(Name, Addr),
    length(Addr, Level),
    refine_goal(Name, Level, Planner),
    update_plan_record(RootName, Name).
plan(RootName, Name, Planner):-
    init_theorem(Name),
    init_goaltree(Name),
    init_plan_record(RootName, Name),
    current_node(Name, Addr),
    length(Addr, Level),
    refine_goal(Name, Level, Planner),
    update_plan_record(RootName, Name).


    % report_on_planning/2
    %
    %
report_on_planning(Name):-
    extract_tactic(Name, Tactic),
    tactic_status(Tactic, Status),
    ((Status = complete) ->
        writef('Planning complete for %t\n',[Name]);
        writef('Planning partially complete for %t\n',[Name])),
    display_plans(Name).

    % dplan/1
    %
    %
dplan(Name):-
    plan(Name, dplan).

    % idplan/1
    %
    %
idplan(Name):-
    plan(Name, idplan).

    % update_plan_record/2
    %
    %
update_plan_record(Name, Name):- 
    recorded(Name, plans(_, SubPlanNames), _),
    extract_tactic(Name, Tactic),
    uniq_recorda(Name, plans(Tactic, SubPlanNames), _).

tactic_status(Tactic, partial):-
    exp_at(Tactic, _, undef).
tactic_status(Tactic, complete):-
    \+ exp_at(Tactic, _, undef).

goaltree_status(Name, Status):-
    extract_tactic(Name, Tactic),
    tactic_status(Tactic, Status).

update_plan_record(RName, Name):-
    \+ RName = Name,
    recorded(RName, plans(Tactic, SubPlanNames), _),
    union([Name], SubPlanNames, NewSubPlanNames),
    uniq_recorda(RName, plans(Tactic, NewSubPlanNames), _),
    update_plan_record(Name, Name).

    % init_theorem/1
    %
    %
init_theorem(Name):-
    theorem(Name, _, _).
init_theorem(Name):-
    \+ theorem(Name, _, _),
    lib_load(thm(Name)).

    % init_plan_record/2
    %
    %
init_plan_record(Name, Name):-
    recorded(Name, plans(_, SubPlanNames), _),!,
    delete_plan_records(SubPlanNames),
    uniq_recorda(Name, plans(_, []), _).
init_plan_record(_, Name):-
    uniq_recorda(Name, plans(_, []), _).

    % delete_plan_record/1
    %
    %
delete_plan_records([]).
delete_plan_records([Plan|Plans]):-
    recorded(Plan, plans(_, SubPlanNames), Ref),
    delete_plan_records(SubPlanNames),
    erase(Ref),
    delete_plan_records(Plans).

    % refine_goal/3
    %
    %
refine_goal(Name, UpperBound, dplan):-
    set_planner(dplan),
    refine_goal_(Name, 30, UpperBound).
refine_goal(Name, UpperBound, idplan):-
    set_planner(idplan),
    bound(LowerBound),
    writef('Depth bound set to %t\n', [LowerBound]),
    current_node(Name, Addr),
    delete_branch(Name, Addr),
    refine_goal_(Name, LowerBound, UpperBound).
refine_goal(Name, _, _).
% refine_goal(Name, _, _):-
%    report_on_planning(Name).


    % refine_goal_/3
    %
    %
refine_goal_(Name, LowerBound, UpperBound):-
    next_open_node(Name, LowerBound, UpperBound),
    refine_node(Name, LowerBound, UpperBound),
    fail.
refine_goal_(Name, _, _):-
    open_nodes(Name, []).

    % next_open_node/3
    %
    %
next_open_node(Name, _, _):-
    open_nodes(Name, []),!,
    fail.
next_open_node(Name, _, _):-
    current_node(Name, Addr),
    planning_failure(Name, Addr),
    retract(planning_failure(Name, Addr)),
    init_goaltree(Name),!,
    fail.
next_open_node(Name, LowerBound, UpperBound):-
    open_nodes(Name, [Addr|_]),
    length(Addr, Level),
    ((Level < UpperBound);
     (Level > LowerBound)),!,
    fail.
next_open_node(Name, LowerBound, UpperBound):-
    open_nodes(Name, [Addr|_]),
    length(Addr, Level),
    Level >= UpperBound,
    Level =< LowerBound,
    new_current_node(Name, Addr).
next_open_node(Name, LowerBound, UpperBound):-
    next_open_node(Name, LowerBound, UpperBound).

    % refine_node/3
    %
    %
refine_node(Name, LowerBound, UpperBound):-   
    planner(dplan),
    current_node(Name, Addr),
    length(Addr, Level),
    expand_goal(Name, Addr, Mthd, _, N),!.
refine_node(Name, LowerBound, UpperBound):-   
    planner(idplan),
    current_node(Name, Addr),
    length(Addr, Level),
    Level < LowerBound,
    expand_goal(Name, Addr, Mthd, _, N),!.
refine_node(Name, LowerBound, UpperBound):-   % backtrack to nearest
    current_node(Name, Addr),                 % (method) choice point
    nearest_choice_point(Name, Addr, NAddr),  
    length(NAddr, NUpperBound),
    NUpperBound >= UpperBound,
    writef('\nBacktracking to %t (choice point)\n', [NAddr]),
    move_to_node(Name, NAddr),
    current_method(Method),
    skeleton(Method, Mthd),
    apply_method(Name, Mthd, _, _, _, N),!.
refine_node(Name, LowerBound, UpperBound):-   % backtrack to nearest
    planner(dplan),
    current_node(Name, Addr),
    nearest_patch_point(Name, Addr, NAddr, _),     
    length(NAddr, NUpperBound),
    NUpperBound >= UpperBound,
    writef('\nBacktracking to %t (patch point)\n', [NAddr]),
    move_to_node(Name, NAddr),
    current_method(Method),
    skeleton(Method, Mthd),
    delete_lemmas,
    apply_critic(Name, Mthd, _, _, _, N),!.   
refine_node(Name, _, _):-
    current_node(Name, Addr),
    length(Addr, Depth),
    writef('\nFailed at depth %t\n', [Depth]),
    assert(planning_failure(Name, Addr)),!.
    

    % step_case_goal/2
    %
    %
step_case_goal(Name, Addr):-
    node(Name, Addr, Hyps==>_, _, _, _, _, _),
    induction_hyp(_, Hyps).

    % non_speculative_goal/2
    %
    % 
non_speculative_goal(Name, Addr):-
    node(Name, Addr, _==>G, _, _, _, _, _),
    matrix(_, M, G),
    \+ contains_meta_variables(M).

set_planner(Planner):-
    retractall(planner(_)),
    assert(planner(Planner)).
    %  display_planner(Planner).

    % bound/1
    %
    %
bound(B) :- genint(N), bound(N,B).
bound(0,4).
bound(N,B) :- N>0, N1 is N-1, bound(N1,B1),delta(N,D), B is B1+D.
delta(_,3).

    % expand_goal/5
    %
    %
expand_goal(Name, Addr, _, _, 0):-
    new_current_node(Name, Addr),
    closed_node(Name, Addr),!.
expand_goal(Name, Addr, Mthd, Pre, NumSGs):-
    new_current_node(Name, Addr),
    delete_branch(Name, Addr),
    display_sequent(Name, Addr),
    method(method, MthdName/Arity),
    functor(Mthd, MthdName, Arity),
    expand_node(Name, Mthd, MthdName, Arity, Pre, NumSGs),!.

expand_node(Name, Mthd, MthdName, Arity, Pre, NumSGs):-
    apply_method(Name, Mthd, MthdName, Arity, Pre, NumSGs),!.
expand_node(Name, Mthd, MthdName, Arity, Pre, NumSGs):-
    apply_critic(Name, Mthd, MthdName, Arity, Pre, NumSGs),!.

    % apply_method/2
    %
    % Applicability of proof methods
    %
apply_method(Name, Method):-
    current_goaltree(ConjName),
    method(method, Name/Arity),
    apply_method(ConjName, Method, Name, Arity, _, _),
    display_node(ConjName).

    % apply_method/6
    % 
    % Applicability of proof methods
    %
apply_method(ConjName, Method, Name, Arity, Pre, NumSGs):-
    current_node(ConjName, Addr),
    node(ConjName, Addr, Input, open, _, _, _, _),
    functor(Method,Name,Arity),
    apply(method,[Method,Input,Pre,Effects,Subgoals,SubstL]),
    eval_mthd_preconds(Method, Pre, ConjName, Addr),
    eval_conditions(Effects),
    propagate_effects(Subgoals, ConjName, Addr, Method, SubstL, NumSGs).
apply_method(ConjName, Method, Name, Arity, Pre, NumSGs):-
    current_node(ConjName, Addr),
    node(ConjName, Addr, Input, closed, _, _, PreL, _),
    functor(Method, Name, Arity),
    select_pre(Method, Pre, PreL, NewPreL),
    delete_branch(ConjName, Addr),
    apply(method,[Method,Input,Pre,Effects,Subgoals,SubstL]),
    eval_conditions(Effects),
    propagate_effects(Subgoals, ConjName, Addr, Method, SubstL, NumSGs),
    record_preconds(ConjName, Addr, NewPreL).
    

    % propagate_effects/6
    %
    %
propagate_effects(Subgoals, ConjName, Addr, Method, SubstL, NumSGs):-
    map_list(Subgoals, SG:=>NSG,
                       apply_annsubst_list(SubstL, SG, NSG),
             NSubgoals),
    extend_goaltree(ConjName, Addr, Method, SubstL, NSubgoals, NumSGs),
    display_method(Method, Addr, NumSGs).

    % apply_critic/6
    %
    % Applicability of proof critics
    %
apply_critic(ConjName, Method, Name, Arity, _, NumSGs):-
    functor(Method, Name, _),
    Critic =.. [Name, Type],
    recorded(Name,critic(_,_),_),
    current_node(ConjName, Addr),
    node(ConjName, Addr, _, _, _, _, _, _),
    apply(critic,[Critic,ConjName,Preprocess,Preconds,Effects]),
    eval_conditions(Preprocess),
    eval_critic_preconds(Critic, Preconds, ConjName, Addr),
    writef('\n>>>>> INVOKING %t CRITIC <<<<<\n\n',[Type]),
    delete_branch(ConjName, Addr),
    call_conjunction(Effects),!.

    % eval_mthd_preconds/4
    %
    % 
eval_mthd_preconds(_, Pre, _, _):-            % Pre already evaluated
    apply(method,[Mthd, _, Pre, _, _, _]),
    ground(Mthd),!.
eval_mthd_preconds(Mthd, Pre, Thm, Addr):-    % Pre requires evaluation
    functor(Mthd, Name, _),                   % but no critics for Mthd
    \+ recorded(Name,critic(_,_),_),!,
    node(Thm, Addr, Input, _, _, _, _, _),
    apply(method,[Mthd, Input, Pre, _, _, _]),
    call_conjunction(Pre),
    record_preconds(Thm, Addr, []).  % Previously [Pre] need to distinguish
                                     % between tried and untried instantiations.
eval_mthd_preconds(Mthd, _, Thm, Addr):-      % Pre requires evaluation
    functor(Mthd, Name, _),                   % critics for Mthd
    recorded(Name,critic(_,_),_),
    node(Thm, Addr, Input, _, _, _, _, _),
    apply(method,[Mthd, Input, Precond, _, _,_]),
    eval_preconds(Precond, EvalPrecond),
    update_preconds(Thm, Addr, EvalPrecond),
    fail.
eval_mthd_preconds(Mthd, Pre, Thm, Addr):- 
    node(Thm, Addr, _, _, _, _, Preconds, _), % for Pre from recorded
    elim_and_choices(Preconds, NPreconds),
    select_pre(Mthd, Pre, NPreconds, NewPreconds),
    record_preconds(Thm, Addr, NewPreconds).

    % select_pre/3
    % 
    % Select next instantiation
    % for Pre from recorded
    % preconditions
    %
select_pre(Mthd, Pre, Preconds, RPreconds):-
    select(Pre, Preconds, RPreconds),
    \+ member(false, Pre),
    apply(method,[Mthd, _, Pre, _, _, []]).
select_pre(Mthd, Pre, Preconds, RPreconds):-
    select(Pre, Preconds, RPreconds),
    \+ member(false, Pre),
    apply(method,[Mthd, _, Pre, _, _, [_|_]]).


    % eval_critic_preconds/4
    %
    %
eval_critic_preconds(_, Pre, Thm, Addr):-  
    node(Thm, Addr, Input, _, _, _, PreL, _),
    call_conjunction(Pre).

elim_and_choices(PreListAll, NewPreList):-
        member([wave_occ_at(_, _, _),
                wave_rule_match(_, _, _, _),_|_], PreListAll),
	elim_and_choices_(PreListAll, NewPreList),!.
elim_and_choices(PreListAll, PreListAll).

elim_and_choices_([], []).
elim_and_choices_([H|T], [H|NewT]):-
	H = [wave_occ_at(_, Pos, _),
             wave_rule_match(_, _, _, _),
             _|_],!,
        elim_occs(Pos, T, NewT1),
        elim_and_choices_(NewT1, NewT).

elim_occs(_, [], []).
elim_occs(Pos, [H|T], NewT):-
	H = [wave_occ_at(_, NPos, _),
             wave_rule_match(_, _, _, _),
             _|_],
        \+ Pos = NPos,!,
        elim_occs(Pos, T, NewT).
elim_occs(Pos, [H|T], [H|NewT]):-
        elim_occs(Pos, T, NewT).
	
        % eval_preconds/2
        %
        %
eval_preconds(Pre, EPreL):-
	findall(EPre, partial_eval(Pre, EPre), EPreL),!.

        % partial_eval/2
        %
        %
partial_eval([Pre|RestPre], [Pre|ERestPre]):-
	call(Pre),
        partial_eval_list(RestPre, ERestPre).

        % partial_eval_list/2
        %
        %
partial_eval_list([], []).
partial_eval_list([Pre|Rest], [Pre|ERest]):-
        call(Pre),
        partial_eval_list(Rest, ERest). 
partial_eval_list([Pre|Rest], [false|ERest]):-
        \+ call(Pre),
	partial_eval_list(Rest, ERest).

        % eval_conditions/1
        %
        %
eval_conditions(L):- call_conjunction(L),!.

        % Trivial utility to execute conjunctions represented as lists.
call_conjunction([]) :- !.
call_conjunction(L) :- list2conj(L,C),!,call(C).
        % Coded slightly weird to allow bi-directional use:
list2conj([H,Ht|T],(H,T1)) :- !,list2conj([Ht|T],T1).
list2conj([H],H).

init_subst_list(Name):-
    uniq_recorda(Name, subst([]), _).

update_subst_list(_, []).
update_subst_list(Name, NSubstL):-
    recorded(Name, subst(SubstL), _),
    append(SubstL, NSubstL, NewSubstL),
    uniq_recorda(Name, subst(NewSubstL), _).

    % extract_tactic/2
    %
    % Tactic extraction
    %
extract_tactic(Name, Tactic):-
    extract_tac(Name, [], Tactic).
extract_tac(Name, Addr, Tactic):-
    leaf_node(Name, Addr),
    node(Name, Addr, _, _, Tactic, _, _, 0).
extract_tac(Name, Addr, Tactic then Tactics):-
    branch_node(Name, Addr),
    node(Name, Addr, _, _, Tactic, _, _, N),
    extract_tac_list(Name, 1, N, Addr, Tactics).

extract_tac_list(_, M, Max, _, []):-
    M > Max.
extract_tac_list(Name, M, Max, Addr, [Tactic|Tactics]):-
    extract_tac(Name, [M|Addr], Tactic),
    N is M + 1,
    extract_tac_list(Name, N, Max, Addr, Tactics).

    % extract_subst_list/2
    %
    %
extract_subst_list(Name, SubstL):-
    extract_subs(Name, [], SubstL).

    % extract_subst/3
    %
    %
extract_subs(Name, Addr, SubstL):-
    leaf_node(Name, Addr),
    node(Name, Addr, _, _, _, SubstL, _, 0).
extract_subs(Name, Addr, SubstL):-
    branch_node(Name, Addr),
    node(Name, Addr, _, _, _, SubstL1, _, N),
    extract_subs_list(Name, 1, N, Addr, SubstL2),
    append(SubstL1, SubstL2, SubstL).

    % extract_subst_list/5
    %
    %
extract_subs_list(_, M, Max, _, []):-
    M > Max.
extract_subs_list(Name, M, Max, Addr, SubstL):-
    extract_subs(Name, [M|Addr], SubstL1),
    N is M + 1,
    extract_subs_list(Name, N, Max, Addr, SubstL2),
    append(SubstL1, SubstL2, SubstL).

    % apply_subst_to_goaltree/2
    %
    % Apply subst list to goaltree
    %
apply_subst_to_goaltree(_, []).
apply_subst_to_goaltree(Name, Subst):-
    apply_subst_to_node(Name, [], Subst).

    % apply_subst_to_goaltree/3
    %
    %
apply_subst_to_node(Name, Addr, Subst):-
    retract(node(Name, Addr, H==>G, Status, Mthd, SL, Pre, N)),
    apply_annsubst_list(Subst, H, HH),
    apply_annsubst_list(Subst, G, GG),
    assertz(node(Name, Addr, HH==>GG, Status, Mthd, SL, Pre, N)),
    apply_subst_to_goaltree(Name, Addr, N, Subst).


    % apply_subst_to_goaltree/4
    %
    %
apply_subst_to_goaltree(_, _, 0, _).
apply_subst_to_goaltree(Name, Addr, N, Subst):-
    N > 0,
    apply_subst_to_node(Name, [N|Addr], Subst),
    M is N-1,
    apply_subst_to_goaltree(Name, Addr, M, Subst).
    

/*****************************************************************

 GOAL TREE MANAGEMENT:

 A goal tree is represented by a set of entries in prolog's
 recorded database. Entries are keyed under the atom 'node'
 and have the following structure:

      1. name of conjecture
      2. address (integer list)
      3. goal
      4. status (open or closed)     
      5. method name/args
      6. substitution list
      7. precondition(s)
      8. number of subgoals

 ****************************************************************/

% CONSTRUCTORS

    % init_goaltree/1
    %
    %
init_goaltree(Name):-
    delete_goaltree(Name),
    select(Name),
    goal(G), hyp_list(H),
    assertz(node(Name, [], H==>G, open, undef, [], [], 0)),
    retractall(open_nodes(Name, _)),
    assertz(open_nodes(Name, [[]])),
    assertz(current_node(Name, [])),
    uniq_recorda(current_goaltree, Name, _).

    % extend_goaltree/6
    %
    %
extend_goaltree(Name, Addr, Mthd, SubstL, [], 0):-
    retract(node(Name, Addr, Goal, _, _, _, Preconds, 0)),
    update_open_nodes_list(Name, Addr, 0),
    assertz(node(Name, Addr, Goal, closed, Mthd, SubstL, Preconds, 0)),
    extract_subst_list(Name, GlobalSubstL),
    apply_subst_to_goaltree(Name, GlobalSubstL),
    set_planner(dplan),!.
extend_goaltree(Name, Addr, Mthd, SubstL, Subgoals, Num):-
    retract(node(Name, Addr, Goal, _, _, _, Preconds, N)),
    delete_branches(Name, N, Addr),
    assert_subgoals(Name, Addr, 0, Subgoals, Num),
    update_open_nodes_list(Name, Addr, Num),    
    assertz(node(Name, Addr, Goal, closed, Mthd, SubstL, Preconds, Num)),!.

update_open_nodes_list(Name, Addr, 0):-!,
    open_nodes(Name, AddrL),
    retractall(open_nodes(Name, _)),
    remove(Addr, AddrL, NewAddrL),
    assert(open_nodes(Name, NewAddrL)).
update_open_nodes_list(Name, Addr, N):-
    open_nodes(Name, AddrL),
    retractall(open_nodes(Name, _)),
    remove(Addr, AddrL, AddrL2),
    gen_subgoal_addresses(Addr, N, AddrSubs),
    append(AddrSubs, AddrL2, NewAddrL),
    assert(open_nodes(Name, NewAddrL)).

gen_subgoal_addresses(Addr, 0, []).
gen_subgoal_addresses(Addr, M, [NAddr|AddrL]):-
    append([M], Addr, NAddr),
    N is M - 1,
    gen_subgoal_addresses(Addr, N, AddrL).

    % add_node/8
    %
    %
add_node(Name, Addr, _, _, _, _, _, _):-
    node(Name, Addr, _, _, _, _, _, _),
    retract(node(Name, Addr, _, _, _, _, _, _)),
    fail.
add_node(Name, Addr, Goal, Status, Mthd, SubstL, Pre, N):-
    assertz(node(Name, Addr, Goal, Status, Mthd, SubstL, Pre, N)).

    % assert_subgoals/5
    %
    %
assert_subgoals(_, _, Cnt, [], Cnt).
assert_subgoals(Name, Addr, TotSoFar, [G|Gs], Tot):-
    N is TotSoFar + 1,
    assertz(node(Name, [N|Addr], G, open, undef, [], [], 0)),
    assert_subgoals(Name, Addr, N, Gs, Tot).

    % close_branch/3
    %
    %
close_branch(Plan, Addr, Justification):-
    select_goaltree(Plan),
    move_to_node(Plan, Addr),
    current_sequent(Sequent),
    delete_branch(Plan, Addr),
    add_node(Plan, Addr, Sequent, closed, Justification, [], [], 0),
    retract(open_nodes(Plan, AddrL)),
    remove(Addr, AddrL, NAddrL),
    assert(open_nodes(Plan, NAddrL)).

    % update_preconds/3
    %
    %
update_preconds(Name, Addr, Preconds):-
    retract(node(Name, Addr, Goal, _, _, SubstL, PreSoFar, _)),
    append(PreSoFar, Preconds, NewPreconds1),
    remove_duplicates(NewPreconds1, NewPreconds),
    assertz(node(Name, Addr, Goal, open, _, SubstL, NewPreconds, 0)),!.

    % remove_duplicates/2
    %
    %
remove_duplicates([], []).
remove_duplicates([H|T], NewT):-
	member(H, T),
        remove_duplicates(T, NewT).
remove_duplicates([H|T], [H|NewT]):-
        \+ member(H, T),
        remove_duplicates(T, NewT).

    % record_preconds/3
    %
    %
record_preconds(Name, Addr, Preconds):-
    retract(node(Name, Addr, Goal, Status, Mthd, SubstL, _, N)),
    assertz(node(Name, Addr, Goal, Status, Mthd, SubstL, Preconds, N)).

    % record_newgoal/3
    %
    %
record_newgoal(Name, Addr, NewGoal):-
    retract(node(Name, Addr, _, _, _, _, _, _)),
    assertz(node(Name, Addr, NewGoal, open, [], [], _, 0)).


% PREDICATES

leaf_node(Name, Addr):-   node(Name, Addr, _, _,      _, _, _, 0).
branch_node(Name, Addr):- node(Name, Addr, _, _,      _, _, _, N),
                          N > 0.
open_node(Name, Addr):-   node(Name, Addr, _, open,   _, _, _, 0).
closed_node(Name, Addr):- node(Name, Addr, _, closed, _, _, _, _).

% SELECTORS

    % current_goaltree/1
    %
    %
current_goaltree(Thm):-
    recorded(current_goaltree, Thm, _).

    % current_goal/1
    %
    %
current_goal(Goal):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _==>Goal, _, _, _, _, _).

    % current_hyps/1
    %
    %
current_hyps(Hyps):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, Hyps==>_, _, _, _, _, _).

    % current_sequent/1
    %
    %
current_sequent(Sequent):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, Sequent, _, _, _, _, _).

    % current_method/1
    %
    %
current_method(Mthd):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, _, Mthd, _, _, _).

    % current_status/1
    %
    %
current_status(Status):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, Status, _, _, _, _).

    % current_subst/1
    %
    %
current_subst(Subst):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, _, _, Subst, _, _).

    % current_preconds/1
    %
    %
current_preconds(Preconds):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, _, _, _, Preconds, _).

    % current_successful_preconds/1
    %
    %
current_successful_preconds(SPreconds):-
    current_preconds(Preconds),
    findall(P, (member(P, Preconds), 
                \+ member(false, P)), 
            SPreconds).

    % current_subgoal_count/1
    %
    %
current_subgoal_count(Cnt):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, _, _, _, _, Cnt).

% DESTRUCTORS

    % delete_goaltree/1
    %
    %
delete_goaltree(Name):-
    current_node(Name, _),!,
    retractall(current_node(Name, _)),
    retractall(node(Name, _, _, _, _, _, _, _)),
    delete_current_rec(Name).
delete_goaltree(_).

    % delete_goaltree_rec/1
    %
    %
delete_current_rec(Name):-
    recorded(current_goaltree, Name, Ref),
    erase(Ref).
delete_current_rec(_).

    % delete_branch/2
    %
    %
delete_branch(Name, Addr):-
    new_current_node(Name, Addr),
    node(Name, Addr, Goal, _, _, _, _, N),
    add_node(Name, Addr, Goal, open, undef, [], [], 0),
    delete_branches(Name, N, Addr),
    retract(open_nodes(Name, AddrL)),
    union([Addr], AddrL, NAddrL),
    assert(open_nodes(Name, NAddrL)).

    % delete_node/2
    %
    %
delete_node(Name, Addr):-
    retract(node(Name, Addr, _, open, _, _, _, 0)),
    retract(open_nodes(Name, AddrL)),
    remove(Addr, AddrL, NewAddrL),
    assert(open_nodes(Name, NewAddrL)).
delete_node(Name, Addr):-
    retract(node(Name, Addr, _, closed, _, _, _, N)),
    delete_branches(Name, N, Addr).

    % delete_branches/3
    %
    %
delete_branches(_, 0, _).
delete_branches(Name, N, Addr):-
    N > 0,
    delete_node(Name, [N|Addr]),
    M is N-1,
    delete_branches(Name, M, Addr).

% DISPLAY ROUTINES

    % display_planner/1
    %
    %
display_planner(dplan):-
    writef('Invoking depth first planner ...\n').
display_planner(idplan):-
    writef('Invoking iterative deepening planner ...\n').

    % display_plans/1
    %
    %
display_plans(Name):-
    recorded(Name, plans(Tactic, SubPlanNames), _),
    node(Name, [], Sequent, _, _, _, _, _),
    display_conjecture(Sequent, Name),
    print_plan(Tactic),nl,
    reverse(SubPlanNames,RSubPlanNames),
    display_plans_list(RSubPlanNames).
display_plans(_).

    % display_plans_list/1
    %
    %
display_plans_list([]).
display_plans_list([Thm|Thms]):-
    display_plans(Thm),
    display_plans_list(Thms).

    % display_conjecture/2
    %
    %
display_conjecture([]==>G, ThmName):-
    display_conj(G, ThmName).
display_conjecture(Thm, ThmName):-
    Thm \= (_ ==> _),
    display_conj(Thm, ThmName).
    
display_conj(Thm, ThmName):-
    matrix(Binds,Mat,Thm),
    writef('%r\n',['-',60]),
    writef('%t:\n\n',[ThmName]),
    writef('%t\n\n|- %t\n\n',[Binds,Mat]).

    % display_sequent/2
    % 
    %
display_sequent(Name, Addr):-
    node(Name, Addr, (H==>G), _, _, _, _, _),
    length(Addr, D),
    Node =.. [Name,Addr],
    writef( '%r%t\n', ['|',D,Node] ) ,
    print_nllist(H,D,'|'),
    writef('%r==>%t\n',['|',D,G]),!.

    % display_method/3
    %
    %
display_method(Method, Addr, 0):- !,
    length(Addr, D),
    writef('%rTERMINATING METHOD at depth %t: %t\n',['|',D,D,Method]).
display_method(Method, Addr, _):-
    length(Addr, D),
    writef('%rSELECTED METHOD at depth %t: %t\n',['|',D,D,Method]).

    % display_node/1
    %
    %
display_node(Name):-
    current_node(Name, Addr),
    node(Name, Addr, H==>G, Status, Mthd, SubstL, Preconds, Num),
    writef('%r\n',['-',60]),
    writef('Plan node:     %t(%t)\n',[Name,Addr]),
    writef('Status:        %t\n',[Status]),
    writef('Hypotheses:    '),print(H),nl,
    matrix(Q, M, G),
    writef('Quantifiers:   '),print(Q),nl,
    writef('Conclusion:    %t\n',M),
    writef('Method:        %t\n',Mthd),
    writef('Substitutions: '),print(SubstL),nl,
    length(Preconds, L),
    writef('Preconds:      %d\n',L),
    writef('Subgoals:      %d\n',Num),
    writef('%r\n',['-',60]),!.

% GOALTREE NAVIGATION


    % new_current_node/2
    %
    %
new_current_node(Name, Addr):-
    retractall(current_node(Name, _)),
    assertz(current_node(Name, Addr)).

    % move_to_node/2
    %
    %
move_to_node(Name, Addr):-
    new_current_node(Name, Addr).

    % up_goaltree/1
    %
    %
up_goaltree(Name) :- 
    current_node(Name, [_|Addr]),
    move_to_node(Name, Addr).

    % down_goaltree/1
    %
    %
down_goaltree(Name) :- 
    down_goaltree(Name, 1).
down_goaltree(Name, Num):-
    current_node(Name, Addr),
    new_current_node(Name, [Num|Addr]).

    % top_goaltree/1
    %
    %
top_goaltree(Name):-
    move_to_node(Name, []).

    % move_to_open_node/1
    %
    %
move_to_open_node(Name):-
    next_open_node(Name, 0).

    % select_goaltree/1
    %
    %
select_goaltree(Thm):-
    current_goaltree(Thm).
select_goaltree(Thm):-
    theorem(Thm, _, _),
    uniq_recorda(current_goaltree, Thm, _).


    % ancestor_method/3
    %
    %
ancestor_method(Plan, Addr, Mthd):-
        ancestor_method_(Plan, Addr, Mthd).
ancestor_method_(Plan, Addr, Mthd):-
        node(Plan, Addr, _, closed, Mthd, _, _, _).
ancestor_method_(Plan, Addr, Mthd):-
        append([_], NAddr, Addr),
        ancestor_method_(Plan, NAddr, Mthd).

    % method_occ/2
    %
    %
method_occ(Method, Pos):-
    current_goaltree(Plan),
    current_node(Plan, CurrPos),
    nearest_mthd_occ(Plan, CurrPos, Method, Pos).

    % nearest_mthd_occ/4
    %
    %
nearest_mthd_occ(Plan, Pos, Method, Pos):-
    node(Plan, Pos, _, closed, Method, _, _, _).
nearest_mthd_occ(Plan, [_|PrevPos], Method, Pos):-
    nearest_mthd_occ(Plan, PrevPos, Method, Pos).

% nearest_choice_point/3
%
% Locates nearest choice point. Note that it should be
% defined so that it only looks for OR-choice points.
%
nearest_choice_point(Plan, Addr, Addr):-
    node(Plan, Addr, _, closed, _, _, PreL, _), 
    member(Pre, PreL),
    \+ member(false, Pre).
nearest_choice_point(Plan, [_|Addr], NewAddr):-
    nearest_choice_point(Plan, Addr, NewAddr).

    % nearest_patch_point/4
    %
    %
nearest_patch_point(Plan, InitialAddr, PatchAddr, Critic):-
    apply(critic, [Critic, Plan, _, _, _]),
    nearest_patch_point_(Plan, InitialAddr, PatchAddr, Critic),
    move_to_node(Plan, InitialAddr).
nearest_patch_point(Plan, InitialAddr, _, _):-
    move_to_node(Plan, InitialAddr),!,fail.

    % nearest_patch_point_/4
    %
    %
nearest_patch_point_(Plan, PatchAddr, PatchAddr, Critic):-
    move_to_node(Plan, PatchAddr),
    apply(critic, [Critic, Plan, I, P, _]),
    eval_conditions(I),
    eval_conditions(P).
nearest_patch_point_(Plan, [_|CurrAddr], PatchAddr, Critic):-
    nearest_patch_point_(Plan, CurrAddr, PatchAddr, Critic).
    
       
% ABBREVIATIONS 

    % dd/1
    %
    %
dd(N):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    branch_node(Thm, Addr),
    down_goaltree(Thm, N),
    display_node(Thm).

    % dd/0
    %
    %
dd:-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    branch_node(Thm, Addr),
    down_goaltree(Thm, 1),
    display_node(Thm).

    % ud/0
    % 
    %
ud:-
    current_goaltree(Thm),
    up_goaltree(Thm),
    display_node(Thm).

    % dt/0
    % 
    %
dt:-
    current_goaltree(Thm),
    top_goaltree(Thm),
    display_node(Thm).
    
    % dc/0
    %
    %
dc:-
    current_goaltree(Thm),
    display_node(Thm).

    % cg/1
    %
    %
cg(Thm):-
    current_goaltree(Thm).

    % dn/0
    %
    %
dn:-
    current_goaltree(Thm),
    next_open_node(Thm, 0).

    % db/0
    %
    %
db:-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    delete_branch(Thm, Addr).
  
    % pc/0
    %
    %
pc:-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    delete_branch(Thm, Addr),
    plan(Thm, dplan).

    % pn/0
    %
    %
pn:-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    delete_branch(Thm, Addr),
    refine_goal(Thm, Addr).

    % cp/0
    %
    %
cp:-
    current_preconds(PL),
    print_multi_list(PL).

    % csp/0
    %
    % Current successful preconditions.
    %
csp:-
    current_preconds(PL),
    findall(P, (member(P, PL), \+ member(false, P)), SPL),
    print_multi_list(SPL).

    % sg/1
    %
    % Select goaltree for Thm.
    %
sg(Thm):-
    select_goaltree(Thm),
    top_goaltree(Thm).

    % ap/1
    %
    %
ap(N):-
    current_goaltree(Thm),
    current_node(Thm, Addr),
    node(Thm, Addr, _, _, _, _, Preconds, _),
    findall(P, (member(P, Preconds), \+ member(false, P)), SPreconds),
    nth1(N, SPreconds, Precond),
    delete_branch(Thm, Addr),
    expand_goal(Thm, Addr, _, Precond, _).

    % am/1
    %
    %
am(M):-
    apply_method(M, _).

    % ss/1
    %
    %
ss(N):-
    node(N, Addr, _==>G, Status, Mthd, _, _, _),
    matrix(_, M, G),
    (Status = open -> 
        writef('%t(%t)\n%t\n\n', [Status, Addr, M]);
        writef('%t(%t) by %t\n%t\n\n', [Status, Addr, Mthd, M])),
    fail.
ss(_).

dp(N):-
    display_plans(N).

ig(N):-
    init_goaltree(N).

options:-
    write('dc:    Display Current node.'),nl,
    write('dt:    Display Top node.'),nl,
    write('dd(N): Down and Display Nth node.'),nl,
    write('dd:    Down and Display 1st node.'),nl,
    write('dn:    Display Next goal node.'),nl,
    write('ud:    Up and Display node.'),nl,
    write('cg(N): N is the Current Goaltree.'),nl,
    write('cp:    Current preconditions.'),nl,
    write('csp:   Current (successful) preconditions.'),nl,
    write('db:    Delete Current goaltree branch.'),nl,
    write('pc:    Plan from Current node.'),nl,
    write('pn:    Plan current Node.'),nl,
    write('sg(N): Select Goaltree for N.'),nl,
    write('ap(N): Apply the Nth successful precondition instantiation.'),nl,
    write('am(M): Apply method M.'),nl,
    write('dp(N): Display plans for goaltree for N.'),nl,
    write('ss(N): Display snapshot of goaltree for N.'),nl,
    write('ig(N): Initialize goaltree for N.'),nl.



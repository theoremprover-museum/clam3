/*
 * This file contains code to analyse definitions to check if they are
 * recursive, and if so, in which argument and according to which
 * recursive scheme. Most of this code is only called once for each
 * definition (when the definition is loaded). At load-time we store
 * recursive-records which can then be cheaply used at run-time.
 */

        % is_recursive(?Term,?Num,?Scheme,BaseEqs,StepEqs,Conds) Term is a
        % function that is recursive in its Num-th argument according to
        % recursion Scheme, with base-equations BaseEqs and
        % step-equations Step-Eqs. All of the equations (both base-eqns
        % and step-eqn) are of the form Name:Equation where Name is the
        % name of the Oyster theorem that actually proves the equation.
        % If there is more than one step-equation (ie length(StepEqs)>1),
        % then these step-equations will each be prefixed by a
        % condition. The total set of these conditions (disjunctively
        % amounting to "true") are collected in Conds. If there is only
        % one (unconditional) step-equation, then Conds=[].
        % 
        % This predicate is the work-horse for all of recursive/3,
        % base_rule/2 and step_rule/2, and should at some time maybe
        % replace all of them.
        %
        % This predicate is called once-only for every function, and
        % then the results will be stored as recursive/5 terms. Thus,
        % is_recursive will typically not be called by the user.
        % This is because is_recursive/5 is expensive and computes
        % the same results over and over again. 
        %
        % A lot of the work has already been done in is_a_wave_rule/6,
        % so all we have to do to decide that Term is recursive in its
        % Num-th argument according to Scheme is as follows: [0] pick up
        % the step equation for Term (as already computed by
        % is_a_wave_rule/6). [1] pick any wave-argument of Term (as
        % computed by is_a_wave_rule/6).  [2] compute what the lhsides
        % of the base equations should be, [3] check that there are
        % indeed base equations with the appropriate lhsides.
        % 
        % NOTE: we make all kinds of assumptions on the shape of the
        % step equations (see the comments at pick_up_step_eqn/5), which
        % might well turn out to be too restrictive.
        % 
        % Note the use of storing recursion equations as recorded
        % theorem/5 items under the same name as the def for which they
        % are an equation.
        % A.Stevens: 
is_recursive(Term,Nums,Schemes,BaseEqL,StepEqs,Conds) :-
    % [0]:
    pick_up_step_eqn(Term,PosL,Schemes,StepEqs,Conds),
    % [1]:
        % Not clear if we should require the elements of PosL to be
        % length 1 (as below), or if we should use [Num|_] instead...:
    findall(Num,member([Num],PosL),Nums),
    zip(SchemesNums,Schemes,Nums),
    % [2]:
    basegoals_for_func( SchemesNums, Term, BSeqsList ),
    zip(BSeqsListNums,BSeqsList,Nums),
    % [3]:
    functor(Term,F,_),
    map_list(BSeqsListNums,(BSeqs-Num):=>BaseEqs,
            base_goals_all_same_as_rec_eqn_lhs(BSeqs,F,Num,BaseEqs),
            BaseEqL1),
    append(BaseEqL1,BaseEqL).

basegoals_for_func( [Scheme-Num|RestSchemesNums], Term, 
                    [BSeqs|RestBSeqs] ) :-
    copy(Term, STerm ),
    make_ground(STerm),
    freevarsinterm(STerm,Vars),
    untype(VarsTypes,Vars,_),
    guess_type(pure,VarsTypes,STerm, _),
    exp_at(STerm,[Num],Var),
    member(Var:Type, VarsTypes ),
    make_ground(Type),
    !,
    scheme(IScheme,Var:Type,[]==>STerm,BSeqs,_),
    member(Scheme,IScheme),
    basegoals_for_func( RestSchemesNums, Term, RestBSeqs ).

basegoals_for_func([],_,[]).

base_goals_all_same_as_rec_eqn_lhs([],_,_,[]).
base_goals_all_same_as_rec_eqn_lhs([Hs==>G|Ss],F,Num,[FN:Q_Eq|Eqs]):-
    recorded(theorem,theorem(F,eqn,Eq,FN),_),
    instantiate(Eq,G=_ in _,_),
    exp_at(G,[Num],V), \+ hyp(V:_,Hs),
    matrix(Vars,M_Eq,Eq),
    replace_universal_vars(Vars,M_Eq,Q_Eq),
    !,
    base_goals_all_same_as_rec_eqn_lhs(Ss,F,Num,Eqs).


         % update_gaze_graph - Update the gaze graph for the
	 % defined term F.
extend_gaze_graph(F) :-
    findset( Func,
	     ( recorded(theorem,theorem(F,eqn,StepEq,_),_),
	       exp_at(StepEq,[0|_],Func )
	     ),
	     RawFunctors
	   ),
    logic_functors( LogFunctors ), 
    subtract(RawFunctors, [F|LogFunctors], Functors ),
    asserta( gaze( F, Functors ) ).

        % pick_up_step_eqn/5 collects the step-equations for Term. The
        % assumption is that there is either just one step equation
        % (clause 1), or that there are multiple step-equations which
        % all define the same recursive scheme, but under different
        % conditions (second clause). These assumptions will turn out to
        % be far too restrictive, and will have to be
        % relaxed/generalised in the future.  
pick_up_step_eqn(Term,PosL,Schemes,[FN:Q_Eq],[]) :- 
    recorded(wave,wave(FN,Lhs:=>_,genw(left,_),PosL,Schemes,Term),_),
    \+ wave_fronts(_,[],Lhs),
    functor(Term,F,_),
    recorded(theorem,theorem(F,eqn,StepEq,FN),_),
    matrix(Vars,Eq,StepEq),
    replace_universal_vars(Vars,Eq,Q_Eq).

pick_up_step_eqn(Term,PosL,Schemes,StepEqs,Conds) :-
    recorded(wave,wave(_,_=>Lhs:=>_,genw(left,_),PosL,Schemes,Term),_),
    \+ wave_fronts(_,[], Lhs ),
    functor(Term,F,_),
    findall(Q_Cond-(FN:Q_Cond=>Q_Eq),
                           (recorded(theorem,theorem(F,eqn,StepEq,FN),_),
                            matrix(Vars,Cond=>Eq,StepEq),
                            replace_universal_vars(Vars,Cond=>Eq,Q_Cond=>Q_Eq)
                           ),
            Conds_StepEqs),
    Conds_StepEqs \= [],
    zip(Conds_StepEqs,Conds,StepEqs).

        % add_recursive_clause(Term). The above code for is_recursive/5
        % computes the recursive argument, scheme and equations for a
        % particular term, but in fact this information can be computed
        % once and for all for a term-skeleton (ie. containing
        % meta-variables) so that the above code need not be executed
        % every time.
        % add_recursive_clause(Term) adds an extra term to the Prolog
        % record-database for recursive/5.
add_recursive_clause(F) :-
    definition(F/N<==>_), functor(Term,F,N), !,
    is_recursive(Term,Num,Scheme,BEqs,SEqs,Conds),
    skeleton(Term,Skel_Term),
    writef(' adding recursive-record for %t...%f',[F]),
    uniq_recorda(recursive, recursive(Skel_Term,Num,Scheme,BEqs,SEqs,Conds),_),
    writef('done\n').

        % The clauses for recursive/5 are computed at load-time and then
        % cached as recorded items by add_recursive_clause/1 using
        % is_recursive/5.
        %
        % First clause is to convert atomic first arguments to terms of
        % the right arity.
recursive(F,Num,Scheme,BaseEqs,StepEqs,Conds) :-
    definition(F/N<==>_), N\=0, functor(T,F,N),!,
    recursive(T,Num,Scheme,BaseEqs,StepEqs,Conds).
recursive(Term,Num,Scheme,BaseEqs,StepEqs,Conds) :-
    recorded(recursive,recursive(Term,Num,Scheme,BaseEqs,StepEqs,Conds),_).


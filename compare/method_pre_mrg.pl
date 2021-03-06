/*
 * CLAM.v3.2
 *
 * This file contains code for the meta-level predicates
 * used to define the proof methods. The file is divided
 * preconditions and effects.
 *
 */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRECONDITIONS
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% induction_vars/3
%
%
induction_vars(Context, Goal, Vars, Typs):-
        wave_fronts(_, [], Goal),
        freevarsinterm(Goal, FVars),
        findall(OSVarTyps, (subseq(FVars, _, SVars), 
                            \+ SVars = [],
                            map_list(SVars, Var:=>(Var:Typ), 
                                            member(Var:Typ, Context), 
                                     SVarTyps),
                            order_vartyps(SVarTyps, OSVarTyps)), VarTypsL),
        member(VarTyps, VarTypsL), 
        vars_typs(VarTyps, Vars, Typs).


% order_vartyps/2: Hack to get ordering of induction variables
%                  compatible with scheme/5.
%
order_vartyps([V:T], [V:T]).
order_vartyps([V1:pnat,V2:T2], [V1:pnat,V2:T2]).
order_vartyps([V1:T1 list, V2:pnat], [V2:pnat, V1:T1 list]). 


vars_typs([], [], []).
vars_typs([V:T|VTs], [V|Vs], [T|Ts]):-
	vars_typs(VTs, Vs, Ts).

% wave_occ/3
%
%
wave_occ(H, G, VarTyps, IndTerms):-
        var(IndTerms),
        matrix(VTList, M, G),
        append(H, VTList, Context),
        induction_vars(Context, M, Vars, Typs),
        \+ non_wave_occ(M, Vars, _, _, _),
	wave_occ_(M, Vars, IndTerms), 
        vars_typs(VarTyps, Vars, Typs).
wave_occ(H, G, VarTyps, IndTerms):-
        var(IndTerms),
	matrix(VTList, M, G),
        append(H, VTList, Context),
        induction_vars(Context, M, Vars, Typs),
        non_wave_occ(M, Vars, _, _, _),
	wave_occ_(M, Vars, IndTerms), 
        vars_typs(VarTyps, Vars, Typs).
wave_occ(H, G, VarTyps, IndTerms):-
        \+ var(IndTerms).
                

% wave_occ_/3
%
%
wave_occ_(Term, Vars, IndTerms):-
	wave_occ(Term, Vars, _, _, _, IndTerms, _).

% non_wave_occ/5: need to replace with a primary ripple path filter.
%
%
non_wave_occ(Term, Vars, VarsPosL, F, FPos):-
	wave_func(Term, Vars, VarsPosL, F, FPos, FSch, _),
	\+ (wave_rule(_, _, _ => FSch :=> _),
            base_rewrite(FSch)),!.

base_rewrite(FSch):-
	wave_fronts(F, WSpec, FSch),
        make_ground(F),
	forall{Pos\member(Pos-_, WSpec)}:
              (exp_at(F, Pos, Constr),
               oyster_type(_, [Constr], [BaseVal]),
	       replace(Pos, BaseVal, F, BasePatt),
               (func_defeqn(BasePatt, _);
                reduction_rule(BasePatt, _, _))).

% wave_occ/7
%
%
wave_occ(Term, Vars, VarsPosL, F, FPos, IndTerms, Rn):-
        wave_func(Term, Vars, VarsPosL, F, FPos, FSch, VarsMVars),
        wave_rule(Rn, _, _ => FSch :=> RHS),
        wave_fronts(_, WFSpec, RHS),
        \+ (member(_-_/[Type,_], WFSpec), var(Type)),
        % \+ meta_term_occ_at(RHS, _, _), % Prevent spec wave-rules 
        %                                 % motivating an induction.
	zip(VarsMVars, _, MVars),
	\+ (member(T, MVars), var(T)),
        wave_fronts(IndTerms, _, MVars),
        \+ \+ scheme(IndTerms),!.

% wave_func/6
%
%
wave_func(Term, Vars, VAbsPosL, F, FinTerm, FSch, VarsMVars):-
        member(Var, Vars),
        exp_at(Term, VarinTerm, Var),
        append([VarinF], FinTerm, VarinTerm),
        exp_at(Term, FinTerm, F),
        map_list(Vars, V :=> V-VRelPos-VAbsPos, (exp_at(F, VRelPos, V),
	                                         append(VRelPos, FinTerm, VAbsPos)),
                 VRelPosLVAbsPosL),
        zip(VRelPosLVAbsPosL, VRelPosL, VAbsPosL),
	replace_object_vars(VRelPosL, F, FSch, VarsMVars).

replace_object_vars(_, Term, _, _):-
	atomic(Term),!,fail.
replace_object_vars([], Term, Term, []).
replace_object_vars([Var-Pos|PosL], F, FSch, [Var-MVar|VarMVars]):-
	replace(Pos, MVar, F, NF),
	replace_object_vars(PosL, NF, FSch, VarMVars).

% induction_hyp/2
%
%
induction_hyp(V:IndHyp, H):-
	member(V:ih(IndHyp), H).

% wave_occ_at/3
%
%
wave_occ_at(Exp, Pos, SubExp):-
    findall(Pos-SubExp, definite_wave_occ_at(Exp,Pos,SubExp), PosDWaves),
    map_list(PosDWaves, P-L:=> Size-(P-L), size(L,Size), PosSizeDWaves),
    smallest(Pos-SubExp, PosSizeDWaves).
wave_occ_at(Exp, Pos, SubExp):-
    findall(Pos-SubExp,potential_wave_occ_at(Exp,Pos,SubExp),PosPWaves),
    member(Pos-SubExp, PosPWaves).

% ripplable/2
%
%
ripplable(H, G) :-
    wave_occ_at(G, _, L),
    split_wave_fronts(L, _, LHS),
    wave_rule(_, _, C=>LHS:=>_),
    trivial(H==>C).
ripplable(H, G) :-
    wave_occ_at(G, _, LHS),
    wave_rule(_, _, C=>LHS:=>_),
    trivial(H==>C).
ripplable(H, G) :-
    wave_occ_at(G, _, LHS),
    partial_wave_rule_match(LHS, _).

% partial_induction_hyp_match/5
%
%
partial_induction_hyp_match(Var, H, G, NewG, SubstL):-
    not var(H),
    not var(G),
    matrix(Vars, Mat, G),
    wave_fronts(_, [_|_], Mat),
    \+ (meta_variable_occ_at(Mat, _, MVar),
        meta_variable_occ_in_lemma(MVar, _)),
    elim_trailing_waves(Mat, SubstL),
    apply_annsubst_list(SubstL, Mat, L = R in Typ),
    all_waves_beached(L),
    all_waves_beached(R),
    induction_hyp(Var:IndHyp, H),
    matrix(HypVars, SL = SR in _, IndHyp),
    replace_universal_vars(HypVars, [SL,SR], [NSL,NSR]),
    (
     (exp_at(R, Pos, NSR),
      replace(Pos, NSL, R, NewR),
      matrix(Vars, L = NewR in Typ, NewG));
     (exp_at(L, Pos, NSL),
      replace(Pos, NSR, L, NewL),
      matrix(Vars, NewL = R in Typ, NewG))
     ).
%
% Conditional version.
%
partial_induction_hyp_match(Var, H, G, NewG, []):-
    not var(H),
    not var(G),
    matrix(Binds, Cond => Body, G),
    member(Body-NewBody, [(L = R in Typ)-(NewL = R in Typ), 
                          (L => R)-(NewL => R)]),
    wave_fronts(_, [], Cond),
    all_waves_beached(L),
    all_waves_beached(R),
    induction_hyp(Var:IndHyp, H),
    matrix(BindsIH, CondIH => BodyIH, IndHyp),
    elementary([]==>Cond=>CondIH, _),
    member(BodyIH, [LIH = RIH in Typ, LIH => RIH]),
    replace_universal_vars(BindsIH, [LIH,RIH], [MetaLIH,MetaRIH]),
    exp_at(L, Pos, MetaLIH),
    replace(Pos, MetaRIH, L, NewL),
    matrix(Binds, NewBody, NewG).

% Needs rationalizing with code for
% generate_annsubst_list/_ (wave_rule_match.pl)
%
elim_trailing_waves(Form, SubstL):-
        wave_fronts(EForm, WFSpec, Form),
	findall(Pos-WHPos, (meta_term_occ_at(EForm, Pos, MTerm),
                            functor(MTerm, MVar, _),
                            \+ meta_variable_occ_in_lemma(MVar, _),
                            member(Pos-[WHPos]/_, WFSpec)),
                PosL),
        map_list(PosL, (Pos-WHPos):=> Subst, 
                       (exp_at(EForm, Pos, MTerm),
	                MTerm =.. [F|Args],
                        same_length(Args, MArgs),
                        map_list(MArgs, L:=>GL-L, is_grounded(GL), GMArgsL),
                        zip(GMArgsL, GArgs, MArgs),
                        GTerm =.. [F|GArgs],
                        wave_fronts(GTerm, [[]-[WHPos]/[_,out]], AnnGTerm),
                        [ArgPos] = WHPos,
                        arg(ArgPos, GTerm, NGTerm),
                        replace_universal_vars_1(GMArgsL, [AnnGTerm, NGTerm], Subst)),
                SubstL).
                                  
% induction_hyp_match/4
%
%
induction_hyp_match(Var, H, G, SubstL):-
    not var(H),
    not var(G),
    ind_hyp_match(Var, H, G, SubstL).

% ind_hyp_match/4
%
% First-order case
%
ind_hyp_match(Var, H, G, []):-
    not potential_wave_occ(G),
    % matrix(_, L = R in _, G),
    matrix(_, M, G),
    induction_hyp(Var: IndHyp, H),
    instantiate(IndHyp, M, _).
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
    instantiate(IndHyp, ErasedM3, _),
    append(SubstL1, SubstL2, SubstL).
    %
    % Calculate annotations for SubstL
    %
/*
    meta_term_occ_at(ErasedM1, Pos, _),
    exp_at(M, Pos, PWave),
    wave_fronts(EPWave, WFSpec, PWave),
    SubstL = [[LHS,_]],
    EPWave =..  [F|Args],
    same_length(Args, MArgs),
    map_list(MArgs, L:=>GL-L, is_grounded(GL), GMArgsL),
    zip(GMArgsL, GArgs, MArgs),
    GTerm =.. [F|GArgs],
    apply_subst_list(SubstL, GTerm, NewRHS),
    wave_fronts(GTerm, WFSpec, NewLHS),
    replace_universal_vars_1(GMArgsL, [NewLHS, NewRHS], AnnSubst),!.
 */  
    
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
    instantiate(NIndHyp, NewM, _),
    writef('%t==>%t\n',[NewH,NewG]).

build_projection(MTerm, [[SkelMTerm, SkelMArg]]):-
    skeleton(MTerm, SkelMTerm),
    SkelMTerm =.. [_|SkelMArgs],
    member(SkelMArg, SkelMArgs).
    
% coerce_meta_variables/2
%
%
coerce_meta_variables(Term, SubstL):-
    fully_rippled(Term),
    meta_variable_occ_at(Term, _, MVar),
    meta_variable_occ_in_lemma(MVar, Lemma),
    eval_partial_lemma(Lemma, SubstL),
    apply_subst_list(SubstL, Lemma, NewLemma),
    \+ disprove([]==>NewLemma).
coerce_meta_variables(Term, SubstL):-
    erase_potential_waves(Term, _, SubstL),
    meta_variable_occ_at(Term, _, MVar),
    meta_variable_occ_in_lemma(MVar, Lemma),
    apply_subst_list(SubstL, Lemma, NewLemma),
    \+ disprove([]==>NewLemma).


% coerce_sinks/3
%
%
coerce_sinks(Context, L = R in Typ, []):-
    sinks(L, Sink),
    sinks(R, Sink).
coerce_sinks(Context, L = R in Typ, SubstL):-
    sinks(L, SinkL),
    sinks(R, SinkR),
    freevarsinterm(SinkL, VarsinSinkL),
    freevarsinterm(SinkR, VarsinSinkR),
    union(VarsinSinkL, VarsinSinkR, Vars),
    map_list(Vars, V:=> (V:T), member(V:T, Context), NewContext),
    matrix(NewContext, SinkL = SinkR in Typ, Lemma),
    eval_partial_lemma(Lemma, SubstL),
    apply_subst_list(SubstL, Lemma, NewLemma),
    \+ disprove([]==>NewLemma).
coerce_sinks(_, Form, []):-
    sinks(_, [], Form).

% sinks/2
%
%    
sinks(Term, Sink):-
	sinks(_, SPosL, Term),
        member(SPos, SPosL),
	exp_at(Term, SPos, Sink).

%
% Partially instantiated sink contents.
%
/*
ind_hyp_match(Var, H, M, SubstL):-
    wave_occ_at(M, Pos, UnSunkWaveTerm),
    sinkable(Pos,M,Sink),
    wave_occurs_sunk(M, Sink, SunkWaveTerm),
    wave_fronts(_, [SWFPos-[SWHPos]/_], SunkWaveTerm),
    append(SWHPos, SWFPos, AbsSWHPos),
    exp_at(SunkWaveTerm, AbsSWHPos, SWH),
    strip_meta_annotations(SunkWaveTerm, SunkTerm),
    replace_all(SunkWaveTerm, SunkTerm, M, M1),
    wave_occ_at(M1, Pos, UnSunkWaveTerm),
    wave_fronts(UnSunkTerm, [WFPos-[WHPos]/[hard,in]], UnSunkWaveTerm),
    sinks(UnAnnUnSunkTerm, [SPos], UnSunkTerm),
    append(WHPos, WFPos, AbsWHPos),     
    append([_|_], AbsWHPos, SPos),
    exp_at(UnAnnUnSunkTerm, AbsWHPos, WH),
    match_terms(WH, SWH, SubstL),
    apply_subst_list(SubstL, M, NM),
    apply_subst_list(SubstL, H, NewH),
    induction_hyp(Var:IndHyp, NewH),
    instantiate(IndHyp, NewM,_).
*/

% trivial/1
%
%
trivial(H==>C):-
    \+ var(C),
    trivial(H,C).
trivial(_,[]).
trivial(H,[C]):-
    strip_meta_annotations(C,CC),
    elementary(H==>[CC],_).

% sinkable/1
%
%
sinkable(Term):-
	\+ var(Term),
	wave_fronts(_, WFSpec, Term),
	findall(AbsWHPos, (member(WPos-[WHPos]/[_,in], WFSpec),
                           append(WHPos, WPos, AbsWHPos)), AbsWHPosL),
        sinkable(AbsWHPosL, Term).

sinkable([], Term).
sinkable([Pos|PosL], Term):-
	exp_at(Term, Pos, SubTerm),
        sinks(_, [_|_], SubTerm),
	sinkable(PosL, Term). 

/*
sinkable(Term):-
        \+ var(Term),
        wave_fronts(_, [WPos-[WHPos]/[_,in]], Term),
        append(WHPos, WPos, AbsWHPos),
        exp_at(Term, AbsWHPos, SubTerm),
	sinks(_, L1, SubTerm),
        \+ L1 = [].
*/
sinkable(WavePos, Goal, SinkVar):-
    \+ var(WavePos), \+ var(Goal),
    matrix(_, Matrix, Goal),
    exp_at(Matrix, WavePos, SubTerm),
    \+ equality_term(SubTerm),
    sinks(_, SSpec, SubTerm),
    wave_fronts(_, WFSpec, SubTerm),
    member(SPos, SSpec),
    member(WFPos-_/[hard,_], WFSpec),
    \+ SPos == WFPos,
    append(SPos, WavePos, SinkVarPos),
    exp_at(Matrix, SinkVarPos, SinkVar).

equality_term(_ = _ in _).
equality_term(_ = _).


% expression_at/3
%
%
expression_at(G,Pos,Exp):-
    \+ var(G),
    matrix(_,M,G),
    exp_at(M,Pos,Exp),
    \+ atomic(Exp).

% function_defn/2
%
%
function_defn(Exp,Rule):-
    \+ var(Exp),
    func_defeqn(Exp,Rule).


% replace_vars_in_goal/
%
%
replace_vars_in_goal(G, Var, Term, NewG):-
	sinks(_, PosL, G),
	member(Pos, PosL),
	exp_at(G, Pos, Term),!,
	sinks(Term, [[]], STerm),
	replace_all(Var, STerm, G, NewG).
replace_vars_in_goal(G, Var, Term, NewG):-
        replace_all(Var, Term, G, NewG).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% EFFECTS
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/*
 * As replace/3 except position is taken to be
 * with respect to the matrix of the given formula.
 *
 */

replace_in_matrix(Pos, Exp, Form, NewForm):-
    matrix(Vars, Mat, Form),
    replace(Pos, Exp, Mat, NewMat),
    matrix(Vars, NewMat, NewForm).

/***********************************

 sink_expansions/2 

 **********************************/

sink_expansions(G, NewG):-
    matrix(Vars, Mat, G),
    sinks(NMat, SSpec, Mat),
    wave_fronts(_, WSpec, Mat),
    sink_expansions(WSpec, SSpec, NewSSpec),
    sinks(NMat, NewSSpec, NewMat),
    matrix(Vars, NewMat, NewG).

strip_redundant_waves([], Term, Term).
strip_redundant_waves([P|PL], Term, NewTerm):-
    exp_at(Term, P, SubTerm),
    wave_fronts(ESubTerm, _, SubTerm),
    replace(P, ESubTerm, Term, NTerm),
    strip_redundant_waves(PL, NTerm, NewTerm).

%===============================================================================
%
%  Version 2.1 method predicates
%
%===============================================================================
/*
 * This file contains the predicates of the method-language. The
 * connectives that can be used in the method-language (apart of course
 * from the Prolog conjunction ",") live in the file method-conn.pl
 */

        % exp_at(+Exp, ?Pos, ?SubExp): expression Exp contains SubExp at
        % position Pos. Positions are lists of integers representing
        % tree-coordinates in the syntax-tree of the expression, but in
        % reverse order. Furthermore, coordinate 0 represents the
        % function symbol of an expression, thus:
        % exp_at(f(g(2,x),3), [2,1], x) and exp_at(f(g(2,x),3), [0,1], g).
        % The definition from note 349 is extended by defining [] as the
        % position of Exp in Exp. 
        % Fails if Pos is an invalid position in Exp.
        % 
        % NOTE: the tree-coordinates are transparent to wave-fronts
        % which are implemented using special function symbols. Thus,
        % positions in formula are the same whether or not the formula
        % contains wave-fronts. Unfortunately, this means that the
        % "abstract datatype" for wave fronts as defined in the file
        % wave-rules.pl has "leaked" out of that file, and into this
        % predicate.
        % It would maybe have been possible to implement exp_at/3 using
        % the abstract datatype for wave-fronts from wave-rules.pl
        % (using the wavefronts/3 predicate), but this would have been
        % very inefficient: we would end up searching for wave fronts,
        % and deleting and inserting them every time exp_at/3 gets
        % called, even in cases where there ain't no wave fronts at all.
        % Thus, the "leaking" of the abstract datatype is partly a
        % concession to efficiency. 
        % The rules for the behaviour of exp_at/3 with respect to
        % wave-fronts are as follows (see wave-rule.pl for an
        % explanation of the pretty-printing convention):
        % - a ``T'' subterm will always be reported as ``T'' and never as T.
        % - A {T} subterm will always be reported as T and never as {T}.
        % - In both cases the positions are reported as if the ``...'' or
        %   {...} terms were not present. 
        % 
        % r_exp_at/3 does the real work. Its specs are the same as
        % exp_at/3, but it computes the pos-list in the natural order.
        % The final result is reversed before delivered.
        % 
        % We do some special case coding for +Pos. In that case we first
        % do the reverse, and only then plough into the expression,
        % rather than the (in this case silly) generate-and-test
        % behaviour.  The test numbervars(Pos,0,0) is the fastest way of
        % checking if a term is ground. Proving commutativity of
        % addition without the ind_strat speeds up by 25% using this
        % special case trick.
        % 
        % The semantics of exp_at/3 is very close to the Quintus library
        % predicate path_arg/3, except that that does not deal with
        % functors as position 0, and it uses the natural rather than
        % reverse order, so we don't bother to use that.
        % 
        % In fact, we implement exp_at/3 in terms of a slightly more
        % general exp_at/4: exp_at(Exp,[N|P],SubExp,SupSubExp) succeeds if
        % SubExp appears in Exp at position [N|P], and SupSubExp appears
        % in Exp at position P, that is: SupSubExp is the expression
        % immediately surrounding SubExp. This is useful since we often
        % find sequences like: exp_at(Goal,[N|P],Var),exp_at(Goal,P,F)
        % to find the immediately surrounding expression of an occurence
        % of Var. Rather than descending into Goal twice (once to find
        % Var, and once to re-find F), we keep track of the two of them
        % at the same time at no cost. Of course, exp_at/3 can be
        % trivially expressed in terms of exp_at/3. Finally, note that
        % exp_at(_,[],_,_) will always fail (since what would the value
        % of SupSubExp be?), and we therefore need a special clause for
        % exp_at/3 for this case.
        % 
        % This predicate is a very elementary ingredient of not only the
        % set of predicates allowed in methods, but also used a lot in
        % implementing other code, and therefore its efficiency is
        % crucial. 
        % 
        % A possible optimization would be to make a separate version
        % which behaved as path_arg/3 (ie. one that didn't return
        % functors as position 0). Sometimes (often), when we call
        % exp_at/3, we know that we are not interested in such
        % solutions, and we could save a lot of time by not having them
        % generated by exp_at/3.
        %
        % And finally, the code:
        % exp_at/3 succeeds for [] path-expressions (take special action
        % to ignore '@wave_var@' terms). For non-[] path-expressions,
        % hand over to exp_at/4. 
exp_at(Var,[],Var) :- var(Var),!.
exp_at('@wave_var@'(Exp),[],Exp).
exp_at('@sink@'(Exp),[],Exp).
exp_at(Exp,[],Exp) :- \+ (functorp(Exp,'@wave_var@',1) v functorp(Exp,'@sink@',1)).
exp_at(Exp,[N|P],SubExp) :- exp_at(Exp,[N|P],SubExp,_).

        % exp_at/4 fails on [] path-expressions (see comments above),
        % and does special case coding for +Pos (see comments above),
        % before handing over to r_exp_at/4.
exp_at(_,[],_,_) :- fail.
exp_at(Exp, Pos, SubExp, SupSubExp) :-
    numbervars(Pos,0,0),!,
    reverse(Pos,RPos),
    r_exp_at(Exp,RPos,SubExp,SupSubExp).
exp_at(Exp, Pos, SubExp, SupSubExp) :- 
    r_exp_at(Exp, RPos, SubExp, SupSubExp),
    reverse(RPos, Pos).

        % r_exp_at/4 does the real work, and comes in three groups of
        % clauses:
        % [1] fail for vars or atoms
        % [2] deal with Pos of length 1
        % [3] deal with Pos of length >=2
        %     (remember that the case Pos=[] has already been caught by
        %      exp_at/4 above).
        %
        % Group [1] is trivial. Groups [2] and [3] are very similar: two
        % special case clauses to deal with '@wave_var@'/1 and
        % '@wave_front@'/3 terms, and one case that does the "real
        % work". For group [2] the real work consists of enumerating all
        % the arguments, for group [3] the real work consists of
        % enumerating all the arguments and recursing on them.
        %
        % Group [1]: trivial:
r_exp_at(Exp,_,_,_) :- var(Exp),!,fail.
r_exp_at(Exp,_,_,_) :- atomic(Exp), !, fail.
        % Group [2]: unfortunately the two special case clauses cannot
        % start with !, since this would not only cut out the third
        % clause of this group (as intended), but also all the clauses
        % in group [3], which is fatal for mode -Pos. Thus, we need the
        % explicit negations in the 3rd clause of this group.
        % Notice the special action we may have to take at the end of
        % clause 3 in case a generated argument is a '@wave_var@'/1
        % term, which then needs to be skipped.
r_exp_at('@wave_var@'(Exp),[N],SubExp,SupExp) :- 
    r_exp_at(Exp,[N],SubExp,SupExp).

r_exp_at('@sink@'(Exp),[N],SubExp,SupExp) :- 
    r_exp_at(Exp,[N],SubExp,SupExp).

r_exp_at('@wave_front@'(Typ,Dir,Exp),[N],SubExp,'@wave_front@'(Typ,Dir,Exp)) :- 
    r_exp_at(Exp,[N],SubExp,Exp).
r_exp_at(SupExp, [N], Exp, SupExp) :-
    \+ functorp(SupExp,'@wave_front@',3),
    \+ functorp(SupExp,'@wave_var@',1),
    \+ functorp(SupExp,'@sink@',1),
    genarg0(N,SupExp,Exp1),
%%    \+ var(Exp1),
     (functorp(Exp1,'@sink@',1)->Exp1='@sink@'(Exp);
	functorp(Exp1,'@wave_var@',1)->Exp1='@wave_var@'(Exp);Exp1=Exp).

        % Group [3]: This time, the two special case clauses can be cut
        % out with ! since this is the last group in the procedure.
        % Thus, we can avoid the negated functor checks in the last
        % clause of this group. 
r_exp_at('@wave_var@'(Exp),[N1,N2|Ns], SubExp, SupExp) :- !,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at('@sink@'(Exp),[N1,N2|Ns], SubExp, SupExp) :- !,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at('@wave_front@'(_,_,Exp),[N1,N2|Ns], SubExp, SupExp) :- !,
    r_exp_at(Exp,[N1,N2|Ns], SubExp, SupExp).
r_exp_at(Exp, [N1,N2|Ns], SubExp, SupExp) :-
    genarg0(N1,Exp,Arg),
%%    \+ var(Arg),
    r_exp_at(Arg, [N2|Ns], SubExp, SupExp).


        % replace(+Pos, ?NewSub, +OldExp, ?NewExp): NewExp is the result of
        % replacing the subexpression in OldExp at position Pos with NewSub.
        % Either NewSub or NewExp must be instantiated.
        % TODO: It'd be nice if Pos could also be uninstantiated,
        %       allowing for: replace(?Pos,?NewSub,+OldExp,+NewExp)
        % This predicate just does what it's told, and doesn't worry at
        % all about captured variables etc. It is even possible to
        % replace predicate/function symbols....
        % Fails if Pos is an invalid position in OldExp
        %
        % Again, as with exp_at/4, it's easier to deal with the
        % position-list in natural rather than reversed order, so we
        % first reverse it and hand over to r_replace to do the work.
        %
        % Again, as with exp_at/4, the position specifiers are
        % transparent to wave-fronts, and thus this predicate needs to
        % know about the implementation of the wave front terms,
        % resulting in yet another "leak" of the abstract datatype for
        % wave fronts implemented in wave-rule.pl
        % This new leak could of course have been prevented if we only
        % could implement replace/4 in terms of exp_at/4, but I don't
        % think this can be done...
        %
        % Similar rules for the treatment of wave front terms apply for
        % replace/4 as for exp_at/4:
        % - Subterms ``T'' are always replaced including the ``...''
        % - Subterms {T} are always replaced excluding the {...}
        % - Positions are specified as if without wave fronts
replace(Pos, NewSub, OldExp, NewExp) :-
        reverse(Pos,RPos), r_replace(RPos, NewSub, OldExp, NewExp).

replace_multiple( [Pos1|PosR], [Sub1|SubR], OldExp, NewExp ) :-
         replace( Pos1, Sub1, OldExp, IntExp ),
         replace_multiple( PosR, SubR, IntExp, NewExp ).
replace_multiple( [], [], Exp, Exp ).

        % We recursively descend the expression according to the
        % coordinate list. First two clauses are base cases of the
        % descend, taking special action for '@wave_var@'/1 and
        % '@sink@'/1 terms. The third and fourth clauses just skip 
        % wave front terms. The last clause takes arglist apart, 
        % descends Nth argument, and puts arglist back together again.
r_replace([], NewSub, '@wave_var@'(_),'@wave_var@'(NewSub)) :- !.
r_replace([], NewSub, '@sink@'(_),'@sink@'(NewSub)) :- !.
r_replace([], NewSub, _, NewSub).
r_replace([N|Ns], NewSub, '@wave_var@'(VarExp), '@wave_var@'(NewExp)) :- !,
    r_replace([N|Ns], NewSub, VarExp, NewExp).
r_replace([N|Ns], NewSub, '@sink@'(VarExp), '@sink@'(NewExp)) :- !,
    r_replace([N|Ns], NewSub, VarExp, NewExp).
r_replace([N|Ns],NewSub,'@wave_front@'(Typ,Dir,FrontExp),'@wave_front@'(Typ,Dir,NewExp)) :- !,
    r_replace([N|Ns], NewSub, FrontExp, NewExp).
r_replace([N|Ns], NewSub, OldExp, NewExp) :-
    OldExp =.. [F|OldArgs],
    partition_([F|OldArgs], N, PreNth, Nth, PostNth),
    r_replace(Ns, NewSub, Nth, NewNth),
    append(PreNth, [NewNth|PostNth], [NewF|NewArgs]),
    NewExp =.. [NewF|NewArgs].

        % surrounding_term( +Pos, +Term, -SurTerm, -STPos )
        % succeeds iff SurTerm is a term in Term at position STPos
        % that properly nests within it term position Pos

surrounding_term( Pos, Term, SurTerm, STPos ) :-
      reverse( Pos, RPos ),
      surr_term( RPos, Term, SurTerm, [], STPos ).
surr_term( [_|_], Term, Term, STPos, STPos ).
surr_term( [H|T], Term, SurTerm, CurPos, STPos ) :-
    exp_at( Term, [H], SbTerm ),
    surr_term( T, SbTerm, SurTerm, [H|CurPos], STPos ).

        % object_level_term(+X) succeeds iff X is ground and does not
        % contain wave-fronts or sink notations.
        % Notice that this is the third predicate which knows about the
        % internal representation of wave fronts. I don't know how to
        % implement this predicate using just the abstract
        % representation provided by wavefronts/3. Just saying:
        % wave_fronts(X,[],X) is not good enough, since it would pass
        % terms that only contain {...} bits, which we definitely don't
        % want. 
object_level_term(X) :- groundp(X), \+ appears('@wave_var@',X),
                                    \+ appears('@sink@',X).

        % nr_of_occ(?SubExp, +SupExp, ?N): SubExp occurs exactly N times
        % in SupExp. 
        % NOTE: failure indicates that SupExp does not occur in SupExp,
        %       thus: N is never bound to 0.
nr_of_occ(Exp, Exp, 1).
nr_of_occ(SubExp, SupExp, N) :-
    SupExp =.. [_|Args],
    findall(M, (member(Arg, Args),nr_of_occ(SubExp,Arg,M)), Ms),
    Ms \= [],
    sum(Ms, N).

        % wave_occ(+Term,?Var,?VarPos,?F,?FPos, ?Scheme,?Rule): Var
        % occurs in Term, somewhere inside subterm F, in a wave-position
        % of type Scheme, defined by Rule, for which F is the
        % wave-function. VarPos is posn. of Var in F, FPos is posn. of F
        % in Term.
        %
        % It's not clear what the most efficient order of the conjuncts
        % below is: 1,2,3,4 or 1,2,4,3...
/*
wave_occ(Term,Var,Sch) :-
    exp_at(Term,VarinTerm,Var),
    append([VarinF|Pos],FinTerm,VarinTerm),
    exp_at(Term,FinTerm,F),
    skeleton(F, SkelF),
    wave_rule(_,_,_ => L :=> _),
    wave_fronts(SkelF, _, L),
    exp_at(SkelF, [VarinF|Pos], Sch),
    \+ var(Sch).
  
*/  
    % This restricts induction suggestions to recursive definitions.
    % This is a hack :-(  The proof critic  for patching  recursion
    % analysis (note 839) will eliminate this unnatural restriction.

        % replace_all(+OldSub,+NewSub,+Exp,?NewExp): NewExp is the
        % result of replacing all occurrences of OldSub with NewSub in
        % Exp.  We just use the Oyster object-level substitution, since
        % this already deals with capture of variables etc.
        %
        % Sometimes the Oyster predicates s/4 fails, so we catch this
        % failure below. Notice that this is only allowed because we
        % never backtrack over s/4 (because of the mode of replace_all/4).
replace_all(OldSub,NewSub,Exp,NewExp) :- s(Exp,[NewSub],[OldSub],NewExp),!.
replace_all(_,_,Exp,Exp).

%***** TODO This will probably be obsoleted as the new general wave-rule
%***** mechanism is implemented.

        % wave_rule(?WaveFunc,?WavePos,?WaveTerm,?RuleName:Rule):
        % Rule is a waverule whose wave-function (symbol and arity)
        % matches WaveFunc; Rule would be applicable to WaveFunc if the
        % WavePos-th argument of Term would be replaced by WaveTerm. In
        % other words: The lhs of Rule would be applicable to the step
        % case if we applied induction-scheme WaveTerm to the WavePos-th
        % argument of WaveFunc.
        % 
        % Rule is the theorem corresponding to the wave-rule (ie
        % something using = or => as a top-level connective, and not the
        % wave-rule format using :=>). If you want to wave-rule format
        % (the :=> structure), use wave_rule/3 instead.
        % 
        % Remember that wave-rules are of the form:
        % 
        %       F(B1(U11,...,U1m), ... , Bn(Un1,...,Unm)) :=>
        %          BB(F1(U11,...,Un1), ... , Fm(U1m,...,Unm))
        % 
        % In this notation, the arguments to wave_rule/4 are:
        % wave_rule(F(_,...,_),Ni,Bi(_,...,_),Rulename:Rule)
        % 
        % All that wave_rule/4 does is access the cached information
        % about wave rules which is computed at load-time by
        % add_wave_rule.  The below is made to behave very much like the
        % "old" (non-wave-front) version of this predicate. This has the
        % advantage that the preconditions of the induction method can
        % stay the same, but might not be the ultimately correct thing
        % to do...
wave_rule(F,Ni,Bi,RuleName:Rule) :-
    recorded(wave, wave(RuleName, _, _, NList, BiList, F),_), % genw(left,_),
    recorded(theorem,theorem(_,_,Rule,RuleName),_),
    zip(NsBis,NList,BiList),
    member(Ni-Bi,NsBis).

        % wave_rule(?RuleName, ?Type_and_Dir, ?Rule): Rulename is the name of a
        % wave-rule and Rule is the wave-rule structure, ie a term of
        % the form L:=>R with L and R the left- and right-hand-side of
        % the wave-rule, including annotations of wave-fronts and with
        % all universal variables replaced by meta-variables.
        %
        % Again, this structure is stored at load-time by add_wave_rule,
        % and we just do a lookup here. 

wave_rule(RuleName,Type_and_Dir,Rule) :-
       recorded(wave, wave(RuleName,Rule,Type_and_Dir),_).

        % reduction_rule(?Exp,?RuleName:?Rule,?Pos) :-
        % RuleName is the name of an equality which is a reduction rule.
        % Rule is the equality, with all universally quantified
        % variables replaced by meta-(Prolog) variables.
        % Pos is the position in Exp which is being rewritten. 
        %
        % A reduction rule is a rule which either removes a constant
        % expression, or which is a wave rule where the wave front is a
        % type constructor. 
        %
        % These things are stored at load time, so all we have to do is
        % to access the cached representation.
reduction_rule(Exp,RuleName:Rule,Pos) :-
    recorded(reduction,reduction(Exp,RuleName:Rule,Pos),_).

        % equal_rule(?Exp,?RuleName:?Rule,?Pos) :-
        % RuleName is the name of an equivalence which allows us to
        % replace some sentence with an equality.
        % Rule is the equivalance expressed as rewrite rule, 
        % with all universally quantified variables replaced by prolog variables.
        %
        % These things are stored at load time, so all we have to do is
        % to access the cached representation.        
equal_rule(Exp, RuleName:Rule) :-
    recorded( equal, equal( Exp, RuleName:Rule ), _ ).

        % cancel_rule(?Exp,?RuleName:?Rule) :-
        % RuleName is the name of an equation which allows us to
        % replace Exp with some term that is an instance of one of
        % its proper subterms.  I.e. to wholely or partly cancel Exp.
        %
        % These things are stored at load time, so all we have to do is
        % to access the cached representation.
cancel_rule(Exp, RuleName:Rule) :-
    recorded( cancel, cancel( Exp, RuleName:Rule ), _ ).
/* A. Ireland 
 * cancel_rule(LL,Rule:C=>LL:=>RR):-
 *		wave_rule(Rule,genw(_,_),C=>L:=>R),
 *		wave_fronts(LL,[[_,1]-_/_,[_,1]-_/_],L),
 *		wave_fronts(RR,_,R).
 */
        % subsumes(+S1,+S2) induction scheme S1 subsumes induction
        % scheme S2. The proper definition of subsumption is unclear at
        % the moment. Currently, subsumption just stands at being
        % instantiation (ie. term equality or term subsumption between
        % the induction schemes). 
subsumes(S1,S2) :- member(S,S1),instantiation(S,S2).

        % mininal(+Schemes,?Scheme): Scheme is an induction scheme which
        % is a minimal member of Schemes, that is: no other member of
        % Schemes is subsumed by Scheme.
        % 
        % For example:
        % :- minimal([s(x),times(x,y)],S).
        %    S = s(x) ;
        %    S = times(x,y) ;
        % :- minimal([s(x),s(s(x)),times(x,y)],S).
        %    S = s(x) ;
        %    S = times(x,y) ;
minimal(Schemes1,Scheme) :-
    remove_dups(Schemes1,Schemes),
    member(Scheme,Schemes),
    \+ (member(S,Schemes), S\=Scheme, subsumes(Scheme,S)).

        % minimally_subsumes(?Scheme,+Schemes): Scheme is the minimal
        % Scheme which subsumes all members of Schemes. That is: there
        % is no other scheme which also subsumes all members of Schemes
        % but is itself subsumed by Scheme.
minimally_subsumes(Scheme,Schemes) :-
    forall {S\Schemes}:subsumes(Scheme,S),
    \+ (scheme(_,S2),
        Scheme\=S2,
        subsumes(Scheme,S2),
        forall {S\Schemes}:subsumes(S2,S)
       ).

        % type_of(+Exp,?Type) guesses the type of Exp. Current
        % implementation relies on black magic from Jane's code to be
        % found in tactics.pl.
        % Jane's guess_type/2 sometimes returns the
        % same type more then once on backtracking, so we squeeze out
        % multiple same answers here using a setof (bit expensive, since
        % this forces us to compute all guesses all the time (even if
        % the first one is already correct), and we also rely on
        % guess_type returning a finite number of answers, but I cant
        % be bothered doing it any other way (is there any other way?)).
type_of(Exp,Type) :- findset(T,guess_type(Exp,T),Ts),member(Type,Ts).

        % canonical(Exp) checks whether a term Exp is canonical -
        % i.e. built up from the constructor functions of recursive
        % data-types. Implementation is highly hacky for efficiency.
canonical(E) :- var(E),!,fail.
canonical(Exp):-
    oyster_type( _, Constrs, Base ),
    (member(Exp,Base),! ;
    (member(Exp,Constrs);
    (functor(Exp,Constr,_),
     member(Constr,Constrs)))).

        % polarity(?O1,?O2,?F,?N,?P):
        % Function F has polarity P in arg nr. N under orderings O1 and O2.
        % F is positive in arg nr. N under O1 and O2 if:
        % O1(X1,X2) => O2(F(X1),F(X2))
        % where:
        % - X1 and X2 obey: exp_at(F(Xi),N,Xi), and
        % - O1 is a partial ordering on the domain of F (in ints Nt-th arg), 
        % - O2 is a partial ordering on the codomain of F.
        % A positive polarity means that F is monotonic in its Nth arg.,
        % a negative polarity means that F is anti-monotonic in its Nth arg.
        % A zero polarity means that F is neither monotonic nor
        % anti-monotonic in its Nth arg.
        %
        % The below is coded using the auxiliary predicate plrty/5. This
        % is the lookup table for the polarity of all the functions.
        % 
        % The first clause of polarity/5 does straight table-lookup, and
        % the 2nd and 3rd clause apply the following transitivity rules
        % for polarity: + = [+|+] or [-|-] and
        %               - = [-|+] or [+|-]
        % (compare rules for multiplication)
        %
        % Obviously, this table will need to be updated when we are
        % adding new functions, etc.
        % 
        % NOTE: I'm not alltogether sure of the status of the entries in
        % the lookup table. I guess, strictly speaking, CLaM should
        % prove such entries before they can be admitted in the table....
        % (See Blue Book note 539 for more about this issue, and for a
        %  suggestion of how this predicate should have been implemented
        %  (Actually, that note suggests that this predicate has been
        %   implemented in the appropriate way (namely as a special
        %   class of monotonicity theorems), but (as can be seen here),
        %   this is not actually the case (although it could have been
        %   done without too much trouble)))
polarity(leq,leq,_,[],+) :- !. % empty function is positive (think about it!)
polarity(O1,O2,F,N,S) :-
    plrty(F,O1,O2,N,S).
polarity(O1,O2,Exp,[P,Pos|List],+) :-
    exp_at(Exp,[Pos|List],SubExp),
    plrty(SubExp,O1,O,[P],Sign),
    polarity(O,O2,Exp,[Pos|List],Sign).
polarity(O1,O2,Exp,[P,Pos|List],-) :-
    exp_at(Exp,[Pos|List],SubExp),
    plrty(SubExp,O1,O,[P],OneSign),
    (OneSign = (+) -> OtherSign = (-) ; OtherSign = (+)),
    polarity(O,O2,Exp,[Pos|List],OtherSign).
        % replaced by a proper class of monotonicity theorems, as
        % explained in Blue Book note 539).
        % 
        % Notice that the table is organised to use Quintus indexing on
        % the name of the predicate  (functor of first argument
        %
        % simple arithmetic:
plrty(plus(_,_),leq,leq,[1],+).         plrty(plus(_,_),leq,leq,[2],+). 
plrty(exp(_,_),leq,leq,[1],+).          plrty(exp(_,_),leq,leq,[2],+).  
plrty(times(_,_),leq,leq,[1],+).        plrty(times(_,_),leq,leq,[2],+). 
plrty(minus(_,_),leq,leq,[1],+).        plrty(minus(_,_),leq,leq,[2],-).
plrty(double(_),leq,leq,[1],+).         plrty(half(_),leq,leq,[1],+).
plrty(fib(_),leq,leq,[1],+).            plrty(pred(_),leq,leq,[1],+).
        % max/min stuff:
plrty(max(_,_),leq,leq,[1],+).          plrty(max(_,_),leq,leq,[2],+).
plrty(max(_,_),geq,geq,[1],+).          plrty(max(_,_),geq,geq,[2],+).
plrty(min(_,_),leq,leq,[1],+).          plrty(min(_,_),leq,leq,[2],+).
plrty(min(_,_),geq,geq,[1],+).          plrty(min(_,_),geq,geq,[2],+).
        % propositional polarities:
plrty(_#_,=>,=>,[1],+).                 plrty(_#_,=>,=>,[2],+).
plrty(_\_,=>,=>,[1],+).                 plrty(_\_,=>,=>,[2],+).
plrty(_=>_,=>,=>,[2],+).                plrty(_=>_,=>,=>,[1],-).
        % apply{1,2} is interesting: it inherits its polarity from its
        % argument. 
plrty(apply1(_,_),_,_,[1],0).
plrty(apply1(F,_),O1,O2,[2],Sign) :- plrty(F,O1,O2,[1],Sign).
plrty(apply2(_,_,_),_,_,[1],0).
plrty(apply2(F,_,_),O1,O2,[2],Sign) :- plrty(F,O1,O2,[1],Sign).
plrty(apply2(F,_,_),O1,O2,[3],Sign) :- plrty(F,O1,O2,[2],Sign).

        % theorem(?Theorem,?Goal) checks if there exists a known theorem
        % or lemma of name Theorem with goal Goal. This is obviously
        % heavily Oyster dependend. Can be used to backtrack through all
        % current theorems. 
        %
        % Old implementation of this used select/1 to cycle through all
        % theorems, but this is so slooow that we now use our own
        % intermediate representation of theorems (as record-ed theorem/4
        % clauses, see the library.pl) which is indirectly linked to the
        % Oyster representation if needed.
theorem(Thm,Goal) :-
    theorem(Thm,Goal,Type), member(Type,[thm,lemma]).
        % theorem(Thm,Goal,Type) is like theorem/2, but can be used to
        % retrieve other Type's of theorems as well, eg. eqn's, schemes
        % and even synth's (less useful). 
theorem(Thm,Goal,Type) :- 
    recorded(theorem, theorem(_,Type,Goal,Thm), _).
/* A. Ireland
    \+ (cthm=:Thm).     % Current theorem (if any) is excluded from
                        % competition. 
*/
        % complementary_rewrite/3 for the expression Exp the rewrite
        % named Rule (which is complementary to a wave rule) is applicable.
complementary_rewrite(Exp,Dir,Rule:Rewrite):-
    \+ var(Exp),
    recorded(comp_rewrite,
             comp_rewrite(Exp,Dir,Rule:Rewrite),_).

        % func_defeqn/2 for the expression Exp the base-case defining
        % equation named Rule is applicable.
func_defeqn(Exp,Rewrite):-
    recorded(un_defeqn,
             un_defeqn(Exp,Rewrite),_).

        % condition_set/3 if for the expression Exp there exists a
        % complementary set of conditional rewrites then WaveConds
        % and CompConds are instantiated to the associated conditions.
        % That is, WaveConds is instantiated to the conditions which
        % will enable further rippling while CompConds is instantiated
        % to the complementary conditions.

condition_set( Exp, WaveConds, CompConds ) :-
    recorded(condition_set, condition_set( Exp,  WaveConds, CompConds ), _ ).

sym_eval_set( Term, Conds ) :-
    recorded( sym_eval_set, sym_eval_set( Term,  Conds ), _ ).

%*****TODO:  We may need to retain this even after complementary_set
%***** has been properly implemented for a period of backward
%***** compatibility.

        % recursive(?Term,?Nums,?Schemes) Nums is a list of
        % argument-positions and Schemes is a list of recursion
        % schemes, such that Term is recursive in the arguments
        % specified in Nums with recursion schemes specified in 
        % Schemes. Nums and Schemes are ``in sync'': the n-th
        % argument of Nums corresponds to the n-th argument of 
        % Schemes.  
        % recursive(?Term,?Nums,?Schemes,?Conds) is as recursive/3, but
        % Term is defined using conditional step-equation. Conds is the
        % list of all conditions on the step-equations (presumably
        % together disjunctively amounting to "true").
        % 
        % We have to do the iterated unification between Term and the
        % StepEqs in recursive/4 since we want to phrase the Conds in
        % terms of the variables occuring in Term, whereas the stored
        % Conds (found through recursive/6) are phrased in terms of
        % meta-(Prolog) variables.

recursive(Term,Nums,Schemes,Conds) :-
    recursive(Term,Nums,Schemes,_,StepEqs,Conds1),
    wave_fronts(T,_,Term),
    bind_vars(T,StepEqs),
        % The sort at the end is to decide upon some standard order for
        % disjunctions:
    sort(Conds1,Conds).
bind_vars(_,[]).
bind_vars(T,[Eq|Eqs]) :-
    (_:_=>T=_ in _)=Eq,
    bind_vars(T,Eqs).

        % base_rule(?Func, ?BaseEq): BaseEq is an base-equation for the
        % function Func. 
        % step_rule(?Func, ?StepEqs): StepEqs is a step-equation for Func.
        % If there are more than one step- or base-equation, these will
        % be returned on backtracking. 
        %
        % See recursive.pl for info on how recursive/5 is implemented
        % (using pre-computation and caching).
base_rule(F,BaseEq) :- recursive(F,_,_,BaseEqs,_,_),member(BaseEq,BaseEqs).
step_rule(F,StepEq) :- recursive(F,_,_,_,StepEqs,_),member(StepEq,StepEqs).

        % rewrite(?Pos,+Rule,?Exp,?NewExp): NewExp is the result of
        % rewriting the subexpression in Exp at position Pos using
        % equation L=R in T.
        % Only one of Pos, Exp and  NewExp has to be instantiated, so this
        % can also be used to detect if and where a rewrite rule has
        % been applied, but not to generate all possible applications of
        % a rewrite rule.
        %
        % After computing the formal variables in the rewrite rule
        % (using quantify and untype), we use the Oyster
        % substitution predicate twice, once backwards to find the match
        % between formal and actual variables, and once forwards to do
        % the substitution specified by the rewrite rule.
rewrite(Pos,Rule,Exp,NewExp) :-
    matrix(TypedFormalVars,L=R in _,Rule), 
    untype(TypedFormalVars,FormalVars,_),
    exp_at(Exp,Pos,SubExp),
    s(L,ActualVars,FormalVars,SubExp),
    s(R,ActualVars,FormalVars,NewSubExp),
    replace(Pos,NewSubExp,Exp,NewExp).

        % simplify_rules(?Rules) succeeds if Rules is the set of all
        % base-, step- and wave-equations that we have around. Only
        % really useful in mode simplify_rules(-). 
simplify_rules(Rules) :-
    findall(R, (base_rules(R);step_rules(R);wave_rules(R)), RulesL),
    append(RulesL,Rules).
        % base_rules(?Rules), step_rules(?Rules) and wave_rules(Rules),
        % are like simplify_rules/1, but only return base-, step-, or
        % wave-equations.
base_rules(BaseEqs) :-
    findall(BaseEqL,base_rule(_,BaseEqL),BaseEqLs),
    append(BaseEqLs,BaseEqs).
step_rules(StepEqs) :-
    findall(StepEq,step_rule(_,StepEq),StepEqs).
wave_rules(WaveEqs) :-
    findall(RuleName:Rule,wave_rule(_,_,_,RuleName:Rule),WaveEqs).

        % canonical_form(+Exp,+Rules,?NewExp) NewExp is the result of
        % applying to Exp the rewrite rules from Rules as often as possible to
        % as many subexpressions as possible. This of course only makes
        % sense if Rules is confluent. The elements of the list Rules
        % are supposed to be of the form RuleName:Rule
        %
        % The simplest way of writing canonical_form/3 would be to
        % repeatedly call rewrite, trying as many rules on as many
        % subexpressions as possible. This "pure" version would look
        % simply like:
        %       canonical_form(Exp,Rules,NewExp) :-
        %               member(Rule,Rules),
        %               exp_at(Exp,Pos,_),
        %               rewrite(Pos,Rule,Exp,TmpExp),!,
        %               canonical_form(TmpExp,Rules,NewExp).
        % However, this is incredibly expensive, mainly because we call
        % rewrite on all possible subexpressions of Exp. In the version
        % below, the call to rewrite is expanded in-line, and before we
        % do the expensive Oyster substitution s/4, we see if the SubExp
        % we are about to try and rewrite has at least the right functor
        % and arity for the selected Rule to apply. This simple trick
        % reduces the costs of canonical_form 40-fold...
canonical_form(Exp,Rules,NewExp) :-
    member(_:Rule,Rules),
    matrix(TypedFormalVars,L=R in _,Rule),
        functor(L,F,N),
    untype(TypedFormalVars,FormalVars,_),
    exp_at(Exp,Pos,SubExp),
        functor(SubExp,F,N),
    s(L,ActualVars,FormalVars,SubExp),
    s(R,ActualVars,FormalVars,NewSubExp),
    replace(Pos,NewSubExp,Exp,TmpExp),!,
    canonical_form(TmpExp,Rules,NewExp).
canonical_form(Exp,_,Exp).

        % hyp(?Hyp,?HypList) checks if Hyp is among HypList. The methods
        % carry their own hypothesis list around, rather then using
        % Oyster's hyp_list, since we want to be able to add and remove
        % hypotheses at will and carry around meta-level annotations.
	%
        % CLaM hypothesis lists are lists of hypotheses
        % *OR* variable-terminated (i.e. extensible by unifcation)
	% lists of hypotheses.
	%
	% The latter option is intended to support middle-out (least
	% commitment deduction of hypotheses / addition of meta-level
	% annotations.   
        % 
hyp( M, [H|R] ) :-
    H \= (_:[_|_]),
    !,
    ( M = H ;
      hyp( M, R )
    ).
hyp( M, [_:EL|R] ) :-
    nv_member( M, EL );
    hyp( M, R ).

        % nv_member(?Member,?NV_term_list )
        % Succeeds if Member is a member of the (Prolog-) variable terminated
        % list MV_term_list.  (The latter are used to allow collections
        % of things to be extended middle-out)
        % 
nv_member( _, L ) :-
        var(L),
        !,
        fail.
nv_member( A, [A|_]).
nv_member( A, [_|L]) :-
        nv_member( A, L ).

        % hfree( ?VarList, +HypList )
        % VarList is a list of (distinct) variable names free in the
        % hypothesis list HypList
        % 
hfree( [V|R], H ) :-
    var(V),
    genvar(V),
    \+ hyp( V:_, H ),
    !,
    hfree( R, [V:dummy|H] ).
hfree( [V|R], H ) :-
    \+ hyp( V:_, H ),
    hfree( R, [V:dummy|H] ).
hfree( [], _ ).

        % del_hyp( +Hyp, +HypList, -RestHypList )
	% Deletes hypothesis Hyp from HypList giving RestHypList
	% 
del_hyp( M, L, RL ) :-
    selectchk( M, L, RL ),
    !.
del_hyp( M, L, [RHL|RL] ) :-
    select( HL, L, RL ),
    nv_member( M, HL ),
    selectchk( M, HL, RHL ),
    !.

del_hyps( [DH|DL], HL, RL ) :-
    del_hyp( DH, HL, PRL ),
    del_hyps( DL,PRL, RL ).
del_hyps( [], RL, RL ).

        % universal_var(+Seq,?Var): Var (of the form V:T) is a
        % universally quantified variable in the sequent Seq. This can
        % be because V:T appears explicitly quantified in the goal of
        % Seq, or because it appears among the hypotheses (being
        % previously intro'd).
universal_var(_==>G,Var:T) :- matrix(Vars,_,G),member(Var:T,Vars).
universal_var(H==>G,Var:T) :- hyp(Var:T,H), thereis {Pos}: exp_at(G,Pos,Var).

        % instantiate(+G1,?G2,?G2Vals) the variables quantified in G1
        % can be instantiated with the values of G2Vals to obtain G2.
        %
        % NOTE: We require that ALL variables quantified in G1 are
        % instantiated, thus:
        %      instantiate(x:pnat=>y:pnat=>f(x,y),y:pnat=>f(1,y),[1])
        % will NOT succeed!
instantiate(G1,G2,Vals) :- instantiate(G1,G2,[],Vals).
instantiate(Var:T=>G1,G2,Vars,Vals) :-
    T \= j(_),
    T \= nj(_),
    !,instantiate(G1,G2,[Var|Vars],Vals).
instantiate(Var1:T1#G1,Var2:T2#G2,Vars,Vals):-
	replace_all(Var2,Var1,G2,GG2),!,
	instantiate(G1,GG2,Vars,Vals).
instantiate(G1,G2,Vars,Vals) :-
    s(G1,RevVals,Vars,G2),
    reverse(RevVals,Vals).

        % groundp(+X) succeeds iff X is ground.
groundp(X) :- \+ \+ numbervars(X,0,0).

        % metavar(Var) checks if Var is a meta-linguistic variable.
        % Since Prolog is our meta-language, meta-linguistic variables
        % are Prolog variables. You guessed: This predicate is for
        % cosmetic purposes only. We wouldn't want ugly Prolog
        % predicates like var/1 in our code, would we.
metavar(Exp) :- var(Exp).

        % constant(?Term,?Type) succeeds if Term is an object-level
        % term which is a constant in Type.
        % Only useful mode is (+,?).
        % The definition of constants is slightly different from the
        % usual (which are also called canonical constants).
        % For constants, we require that they consist entirely of type
        % constructors and type base-elements, except for positions
        % which are non-recursive in the type constructors (the so
        % called type parameters).
        %
        % Example: Not only is s(0)::nil constant (since it is
        % canonical), but so is x::nil (since x occurs in the
        % non-recursive parameter position of ::/2), but s(0)::x is not.
constant(0,pnat).
constant(s(X),pnat) :- constant(X,pnat).
constant(N,int) :- integer(N).
constant(N,int) :- var(N), genint(N).
constant(nil, _ list).
constant(_H::T,Type list) :-
    % Notice absence of: constant(_H,Type),
    constant(T,Type list).
constant(nil, _ nestedlist).
constant(inl(_)::T, Type nestedlist) :- constant(T, Type nestedlist).
constant(inr(H)::T, Type nestedlist) :-
    constant(H, Type nestedlist),
    constant(T, Type nestedlist).
constant(leaf(N),Type tree) :- constant(N,Type).
constant(tree(L,R),Type tree) :- constant(L,Type tree), constant(R,Type tree).
constant({true},u(1)).
constant(void,u(1)).
%? constant(T1,Type) :- eval(T1,T2), T1\=T2, constant(T2,Type).

        % matrix(?TypedVarList,?T1,?T2): Martrix is the matrix of
        % Formula, that is: all quantifiers at the front of Formula have
        % been removed from Matrix. VarList is the list of variables
        % involved in these quantifiers (in the same order as the
        % quantifiers occured in Formula). Actually, this (currently)
        % only works for universal quantifiers.  
matrix([],T1,T1) :- T1 \= (_:_=>_).
matrix([V:T|Vs],T1,V:T=>T2) :- matrix(Vs,T1,T2).
	
        % precon_matrix(?TypedVarList,?PreConds=>?T1,?T2):
        % T1is the matrix of
        % T2, that is: all quantifiers at the front of Formula have
        % been removed from Matrix. VarList is the list of variables
        % involved in these quantifiers (in the same order as the
        % quantifiers occured in Formula).
        % NOTE: The whole pre-condition stuff only works for *single*
        % pre-conditions.
precon_matrix(VTList, [Cond] => Matrix, Form):-
	var(Form),
	matrix(VTList, Cond => Matrix, Form).
precon_matrix(VTList, [] => Matrix, Form):-
	var(Form),
	matrix(VTList, Matrix, Form).
precon_matrix(VTList, [Cond] => Body, Form):-
        \+ var(Form),
        matrix(VTList, Cond => Body, Form),!.
precon_matrix(VTList, [] => Body, Form):-
        \+ var(Form),
        matrix(VTList, Body, Form).

       % split_into_cases( +CaseAnal, +Goal, -SplitGoal )
       % Given a case-analysis (a list of Name:Type) and a CLaM goal
       % build the list of CLaM goals that result from applying the
       % case-analysis.
       %
       % Try to preserve the Name's, if possible, as the names of
       % the new hypotheses in the case-split goals.

split_into_cases( [Cond|Rest], H==>G, [NH==>G|RestHG] ) :-
    extend_hyps_with_cond( Cond, H, NH ),
    !,
    split_into_cases( Rest, H==>G, RestHG ).
split_into_cases( [], _, [] ).

extend_hyps_with_cond( [V:Cond|Rest], AVars, Hyps, EHyps ) :-
    hyp( V:Cond, Hyps ),
    !,
    extend_hyps_with_cond( Rest, AVars, Hyps, EHyps ).
extend_hyps_with_cond( [V:Cond|Rest], Hyps, EHyps ) :-
    hfree( [V], Hyps ),
    !,
    append(Hyps, [V:Cond], NHyps),
    extend_hyps_with_cond( Rest, AVars, NHyps, EHyps ).
extend_hyps_with_cond( [V:Cond|Rest], AVars, Hyps, EHyps ) :-
    !,
    hfree([VV], Hyps ),
    DD =.. [dd|Rest],
    s( DD, [VV], [V], SDD ),
    SDD =.. [_|SRest],
    append(Hyps, [VV:Cond], NHyps),
    extend_hyps_with_cond( SRest, AVars, NHyps, EHyps ).
extend_hyps_with_cond( [Cond|Rest], AVars, Hyps, EHyps ) :-
    append(Hyps, AVars, Context),
    hfree([V], Context),
    append(Hyps, [V:Cond], NHyps),
    extend_hyps_with_cond( Rest, AVars, NHyps, EHyps ).
extend_hyps_with_cond( [], _, H, H ).

/* New Stuff */

/* META_PRED
 *
 * Definitions of predicates/functions used in the extended
 * method-specification language to support all the fancy
 * ``middle-out deduction'' of induction hypotheses.
 *
 */

%*
%* A.Ireland 11/2/91
%*
%* Extensions to existing meta-predicates used within the pre- and post-
%* condition slots of methods. These predicates were introduced in the
%* course of extending CLAM to deal with rippling existentially
%* quantified goals and rippling-in after weak fertilization 
%* (see note 636 for more details).
%*
%* annotations/4
%* sinks/3
%* mark_sinks/3
%* sink_expansions/3
%* potential_wave_funcs/2
%* strip_sinks/2
%* strip_redundant_sinks/2
%* strip_meta_annotations/2
%* adjust_lhs_pos/3
%* ground_sinks/4
%* matrix/4
%* adjust_existential_vars/4 
%* replace_wave_occ/6
%* replace_definite_occ/4
%* wave_term_at/3
%*/

annotations(T,W,GGG,G):-
		\+ var(G),!,
		wave_fronts(GG,W,G),
		sinks(GGG,T,GG).
annotations(T,W,G,GGG):-
		\+ var(T),
		\+ var(W),
		\+ var(G),
		wave_fronts(G,W,GG),
		sinks(GG,T,GGG).

/* 
 * sinks(?T1, ?SinksSpec, ?T2):
 *
 * T2 is as T1, except that T2 has sinks in the positions specified by, SinksSpec, 
 * a list of term positions. Due to the generous mode of this predicate, sinks/3, 
 * can be used to insert (mode sinks(+,+,-)) or to delete sinks (mode sinks(-,+,+)), 
 * or locate sinks (mode sinks(-,-,+)). At least one of T1 of T2 must be instantiated.
 */
sinks(T,L,TT):- \+ var(TT),!,delete_sinks(TT,L,T).
sinks(T,L,TT):- \+ var(T), \+var(L), !,insert_sinks(T,L,TT).

/* 
 * mark-sinks(+Bindings, +Term, -NewTerm):
 *
 * Bindings is a list of bindings. The Term and NewTerm
 * are identical except that all variables in Bindings 
 * which occur in Term are annotated as sinks in NewTerm.
 */
mark_sinks([],Term,Term).
mark_sinks([Var:_|VarList],Term1,Term3):-
    replace_all(Var,'@sink@'(Var),Term1,Term2),
    mark_sinks(VarList,Term2,Term3),!.
mark_sinks([Var|VarList],Term1,Term3):-
    replace_all(Var,'@sink@'(Var),Term1,Term2),
    mark_sinks(VarList,Term2,Term3).

insert_sinks(Term1,[],Term1).
insert_sinks(Term1,[Pos|PosList],Term3):- !,
    exp_at(Term1,Pos,Exp),
    replace(Pos,'@sink@'(Exp),Term1,Term2),
    insert_sinks(Term2,PosList,Term3).

delete_sinks(Term1,PosList,Term2):-
    delete_sinks(Term1,[],PosList,Term2),!.
delete_sinks(Term1,_,PosList,Term2) :- (atomic(Term1);var(Term1)),!,
                                       Term1 = Term2,PosList = [].
delete_sinks('@sink@'(Term1),Term1Pos,[Term1Pos],Term1):-!.
delete_sinks('@wave_front@'(Typ,Dir,Term1),InPos,OutPos,'@wave_front@'(Typ,Dir,Term2)):- 
    delete_sinks(Term1,InPos,OutPos,Term2),!.
delete_sinks('@wave_var@'(Term1),InPos,OutPos,'@wave_var@'(Term2)):-
    delete_sinks(Term1,InPos,OutPos,Term2),!.
delete_sinks([H1|T1],[N|L],PosList,[H2|T2]):- !,
    delete_sinks(H1,[N|L],PosList1,H2),
    N1 is N + 1,
    delete_sinks(T1,[N1|L],PosList2,T2),!,
    append(PosList1,PosList2,PosList).
delete_sinks(Term1,PosListIn,PosListOut,Term2):-
    Term1 =.. [F|Args],
    delete_sinks(Args,[1|PosListIn],PosListOut,ArgsNew),
    Term2 =.. [F|ArgsNew].
    
sink_expansions([],S,S).
sink_expansions([WF-WHoles/_|Rest],Sinks,[WF|NewSinks]):-
	member(WH,WHoles),
	append(WH,WF,WHPos),
	member(WHPos,Sinks),
	delete(Sinks,WHPos,ModSinks),
	sink_expansions(Rest,ModSinks,NewSinks).
sink_expansions([WSpec|Rest],Sinks,NewSinks):-
	sink_expansions(Rest,Sinks,NewSinks).
	
potential_wave_funcs(G,PWFs):-
	strip_quantifiers(G,M),
	wave_fronts(_,WFS,M),
	findset(Pos,(member([_|Pos]-_/[soft,_],WFS)),PWFs).

cancellable_wave_fronts(CancldRhsInsts,G,Pos,R):-
        adjust_rhs_insts(CancldRhsInsts,R,AdjR),
        replace(Pos,AdjR,G,NewG),
        cancel_rule(NewG,_).

strip_sinks([],[]).
strip_sinks([H==>G|R],[H==>GG|RR]):-
        sinks(GG,_,G),
        strip_sinks(R,RR).


/*
 * strip_redundant_sinks(+T1, -T2):
 *
 * T1 and T2 are lists of goal sequents. The corresponding goal sequents 
 * from each list are identical except that for each goal in T1 which 
 * contains sinks but no wave-fronts the associated goal in T2 contains 
 * no sinks.
 */
strip_redundant_sinks([],[]).
strip_redundant_sinks([H==>G|R],[H==>GG|RR]):-
        wave_fronts(_,[],G),
	sinks(G1,SinkSpec,G),
	findset(SinkPos,(member(SinkPos,SinkSpec),
		         exp_at(G1,SinkPos,Sink),
		         \+ atomic(Sink)),
	        SSinkSpec),
	sinks(G1,SSinkSpec,GG),		     
	strip_redundant_sinks(R,RR).
strip_redundant_sinks([H==>G|R],[H==>G|RR]):-
        strip_redundant_sinks(R,RR).

/*
 * strip_meta_annotations(-T1, +T2):
 *
 * T1 and T2 are identical except that all meta-level 
 * annotations which appear in T2 are eliminated from T1.
 */
strip_meta_annotations([],[]).
strip_meta_annotations([H==>G|R],[H==>GG|RR]):-
	strip_meta_annotations(G,GG),
	strip_meta_annotations(R,RR).

strip_meta_annotations(G,GG):-
	annotations(_,_,GG,G).

/*
 * adjust-lhs-pos(+GoalPos, +Goal, -HypPos ):
 *
 * Given the position GoalPos within the dequantified goal Goal the corresponding 
 * position, HypPos, in the induction hypothesis is calculated. GoalPos and HypPos 
 * differ when the induction conclusion is fully-rippled but the wave-fronts do not 
 * peter-out.
 */
adjust_lhs_pos(GPos,G,HPos):-
	wave_fronts(_,WFs,G),
	member(WF-_,WFs),
	append(Offset,WF,GPos),
	append(Offset,HPos,GPos).
adjust_lhs_pos(GPos,_,GPos).

/*
 * ground-sinks(+Instan, +Lhs, +Rhs, ?SubTerm):
 *
 * {\tt Instan} is a list of sink instantiations. For all members of {\tt Instan}
 * which are prolog variables an instantiation is calculated using {\tt Lhs} and
 * {\tt Rhs}, the left and right hand sides of the current goal. {\tt SubTerm} is
 * a subexpression of {\tt Rhs} in which uninstantiated sinks may occur.
 */
ground_sinks([],_,_,_).
ground_sinks([Var|T],GL,GR,GSub):-
         var(Var),
	 sinks(GR1,GRsinkPos,GR),
         sinks(GL1,GLsinkPos,GL),
	 diff(GLsinkPos,GRsinkPos,SinkPos),
	 instan_sinks(GL1,SinkPos,Var),
         ground_sinks(T,GL,GR,GSub).
ground_sinks([_|T],GL,GR,GSub):-
         ground_sinks(T,GL,GR,GSub).

instan_sinks(Term,[],_).
instan_sinks(Term,[Pos|PosL],Var):-
         exp_at(Term,Pos,Var),
	 instan_sinks(Term,PosL,Var).

/*
 * matrix(?VarList,?EVarList,?Matrix,?Formula):
 *
 * matrix/4 is as matrix/3 except it is extended to deal with
 * existential quantification. EVarList is a list with elements of
 * the form MetaVar-ObjVar:Typ where MetaVar is the prolog variable 
 * which replaces the object-level variable ObjVar in Formula to 
 * give Matrix.
 */
matrix([],[],T1,T1) :- T1 \= (_:_=>_), T1 \= (_:_#_).
matrix([V:T|As],Es,T1,V:T=>T2) :- matrix(As,Es,T1,T2).
matrix(As,[V-V:T|Es],T1,V:T#T2) :- 
			\+ var(T1),
			matrix(As,Es,T1,T2).
matrix(As,[MetaV-VV:T|Es],T1,V:T#T2) :- 
                        var(T1),
		        wave_fronts(VV,_,V),
                        replace_all(V,MetaV,T2,T3),
			matrix(As,Es,T1,T3).

/*
 * adjust_existential_vars(+EVars, +VarBase, -NewEVars, -SubstL):
 *
 * EVars is an association list with elements of the form Term-Var:Typ
 * where the prolog term Term denotes the instantiation for the existential
 * variable Var of type Type. The instantiation may be partial so additional 
 * existential variables may be introduced. To prevent the introduction of
 * name clashes the list of current bindings, VarBase, is required. NewEVars
 * and SubstL denote the refined list of existential variables and the
 * associated substitution list respectively. 
 *
 *
 */
adjust_existential_vars([],_,[],[]).
adjust_existential_vars([Term-Var:Typ|R],Hbase,[Term-Var:Typ|RR],SubstList):- 
	var(Term),!,
	adjust_existential_vars(R,Hbase,RR,SubstList).
adjust_existential_vars([Term-Var:Typ|Rest],Hbase,MetaVars,[Var:Typ,TTerm|RRest]):-
	Term \= Var,!,
	wave_fronts(TTerm,_,Term),
	collect_meta_vars(TTerm,Typ,Hbase,HHbase,MetaVars1),
	adjust_existential_vars(Rest,HHbase,MetaVars2,RRest),
	append(MetaVars1,MetaVars2,MetaVars).
adjust_existential_vars([_|Rest],Hbase,MetaVars,SubstList):-
	adjust_existential_vars(Rest,Hbase,MetaVars,SubstList).

collect_meta_vars(MetaVar,Typ,Hbase,HHbase,[MetaVar-ObjVar:Typ]):- 
	var(MetaVar),
	hfree([ObjVar],Hbase),
        append([ObjVar:Typ],Hbase,HHbase).
%	wave_fronts(ObjVar,[[]-[]/[soft,_]],AnnObjVar).
collect_meta_vars(Atom,_,Hbase,Hbase,[]):- atomic(Atom).
collect_meta_vars([H|T],[HTyp|TTyp],Hbase,HHbase,Vars):-
	collect_meta_vars(H,HTyp,Hbase,Hbase1,HVars),
	collect_meta_vars(T,TTyp,Hbase1,HHbase,TVars),
	append(HVars,TVars,Vars).
collect_meta_vars(Term,Typ,Hbase,HHbase,Vars):-
	Term =.. [_|Args],
	((Typ = BTyp list,
	 collect_meta_vars(Args,[BTyp,Typ],Hbase,HHbase,Vars));
	(collect_meta_vars(Args,[Typ],Hbase,HHbase,Vars))).
			

replace_wave_occ(Var,Sch,EMatrix,F,FPos,NewF):-
			replace_definite_occ(Var,Sch,F,F2),
			replace_potential_occ(FPos,F2,EMatrix,NewF),!.

replace_wave_occ([Var|Vars],Schs,EMatrix,F,FPos,NewF):-
			replace_definite_occ([Var|Vars],Schs,F,F2),
			replace_potential_occ(FPos,F2,EMatrix,NewF),!.

replace_definite_occ(Var,Sch,F,NewF):-
                        \+ Sch = F,
                        findset(Pos,exp_at(F,Pos,Var),PosL),
                        replace_ind_vars(PosL,F,Sch,NewF),!.

replace_definite_occ([],[],NewF,NewF).
replace_definite_occ([Var|Vars],[Sch|Schs],F,NewF):-
                        findset(Pos,exp_at(F,Pos,Var),PosL),
                        replace_ind_vars(PosL,F,Sch,F2),
			replace_definite_occ(Vars,Schs,F2,NewF),!.

replace_ind_vars([],Goal,_,Goal).
replace_ind_vars([Pos|PosL],Goal,Sch,NewGoal):-
                        surrounding_term(Pos,Goal,Sch,Path),!,
			exp_at(Goal,Pos,Exp),\+ var(Exp),
                        replace(Path,_,Goal,NGoal),
                        replace_ind_vars(PosL,NGoal,Sch,NewGoal).
replace_ind_vars([Pos|PosL],Goal,Sch,NewGoal):-
                        exp_at(Goal,Pos,Exp),\+ var(Exp),
                        replace(Pos,_,Goal,NGoal),
                        replace_ind_vars(PosL,NGoal,Sch,NewGoal).
%% replace_ind_vars([_|PosL],Goal,Sch,NewGoal):-
%%                        replace_ind_vars(PosL,Goal,Sch,NewGoal).


replace_potential_occ(FPos,F2,EMatrix,NewF):-
                        replace(FPos,F2,EMatrix,EMatrix2),
                        matrix(_,_,Matrix2,EMatrix2),
                        copy(Matrix2,Matrix3),
                        exp_at(EMatrix,Pos,Matrix3),
                        append(FPos2,Pos,FPos),
                        exp_at(Matrix2,FPos2,NewF).
/*
 * wave_terms_at(+Exp,?Pos,?SubExp)
 *
 *
 * Currently defined in method_pre_new.pl
 *
 *
 * wave_terms_at(Exp,Pos,SubExp):-
 *                       exp_at(Exp,Pos,SubExp),
 *		         \+ atomic(SubExp),
 *                       wave_fronts(_,[_|_],SubExp).
 *
 *
 */

pairs([],[]).
pairs([H|T],LL):-
    map_list(T,I:=>O,O = [H,I],L1),
    pairs(T,L2),
    append(L1,L2,LL).

singles(L,LL):-
    map_list(L,I:=>O,O = [I],LL).

repeated_ind_sugg([Sch],Scheme):- !,
    copy(Sch,MSch),
    member(Sch, Scheme),
    \+ (exp_at(MSch,_,V), var(V),
        MSch=Sch,
        \+ atom(V)).
repeated_ind_sugg(_,_).
    
%
% A.Stevens   
%*****************
%*
%* strip_indhyps/2 - return non-induction hypothesis hyps
%* set_indhyp_state/3, mark_indhyps/3, unmark_indhyps/3
%* Primitives for setting the state and/or position mark
%* on induction hypotheses.
%* ind_hyp_is_raw/1 - Check whether state of most recent
%*                  induction hyothesis implies rippling-out
%*                  has not yet been applied.
%*
%********************

strip_indhyps( [_:[ihmarker(_,_)|_]|R], RH ) :-
    !,
    strip_indhyps( R, RH ).
strip_indhyps( [H|R], [H|RH] ) :-
    strip_indhyps( R,RH ).
strip_indhyps( [], [] ).

set_indhyp_state( [IH:[ihmarker(S,M)|IHyps]|R], S,
                  [IH:[ihmarker(S,M)|IHyps]|RH] ) :-
    !,
    set_indhyp_state( R, S, RH ).
set_indhyp_state( [H|R], S, [H|RH] ) :-
    set_indhyp_state( R, S, RH ).
set_indhyp_state( [], _, [] ).

mark_indhyps( [IH:[ihmarker(S,M)|IHyps]|R], Pos,
              [IH:[ihmarker(S,NM)|IHyps]|RH] ) :-
    !,
    append( Pos, M, NM ),
    mark_indhyps( R, Pos, RH ).
mark_indhyps( [H|R], Pos, [H|RH] ) :-
    mark_indhyps( R, Pos, RH ).
mark_indhyps( [], _, [] ).


unmark_indhyp( [V:Tm|RestTms], Pos, [V:NTm|RestNTms] ) :-
    exp_at( Tm, Pos, NTm ),
    unmark_indhyp( RestTms, Pos, RestNTms ).
unmark_indhyp( [], _, [] ).

ind_hyp_is_raw( H ) :-
    hyp( ihmarker(V,_), H ),
    !,
    var(V).



%*********************
%*
%*  unannotated_hyps( +AH, -H )
%*  - H is hypotheses AH with all annotations stripped.
%*
%********************* 


unannotated_hyps( [_:[Hd|Tl]|RH], UH ) :-
    findall( WSH,
             ( nv_member(V:H,[Hd|Tl]),
               wave_fronts(WSH,_,V:H)
             ),
             WSIH ),
    append( WSIH, RUH, UH ),
    unannotated_hyps( RH, RUH ),
    !.
unannotated_hyps( [V:H|RH], [V:H|RUH] ) :-
    unannotated_hyps( RH, RUH ),
    !.
unannotated_hyps( [_|RH], RUH ) :-

    unannotated_hyps( RH, RUH ).
unannotated_hyps( [], [] ).


%*********************
%*
%*  nonind_hyps( +AH, -H )
%*  - H is hypotheses AH with all annotations stripped, 
%*  ignoring inductions hyps
%*
%********************* 


nonind_hyps( [_:[Hd|Tl]|RH], UH ) :-
    nonind_hyps( RH, UH ),
    !.
nonind_hyps( [V:H|RH], [V:H|RUH] ) :-
    nonind_hyps( RH, RUH ),
    !.
nonind_hyps( [], [] ).


%*********************
%*
%*  adjust_rhs_insts( Cancelled, Rhs, NewRhs)
%* - If Cancelled is a list of the rhs instances from a wave-rule whose wave-fronts
%* have cancelled-out, and Rhs is the wave-rules rhs, NewRhs is the wave-rule
%* rhs with the cancelled rhs instances marked as wave-variables.
%*
%********************

adjust_rhs_insts( CancldRIs, Rhs, NewRhs ) :-
    adj_rhs_insts( CancldRIs, Rhs, [], NewRhs ).
adj_rhs_insts( [ConclRIinWave-ConclRI|RestConclRIs], Rhs, RIPosns, NewRhs ) :-
    replace( ConclRIinWave, ConclRI, Rhs, PartRhs ),
    adj_rhs_insts( RestConclRIs, PartRhs, [ConclRIinWave|RIPosns], NewRhs ).
adj_rhs_insts( [], Rhs, RIPosns, NewRhs ) :-
    functor(Rhs, Func, _),is_hov(Func),!,
    adj_rhs_insts_(Rhs, RIPosns, [_,out], NewRhs).
adj_rhs_insts( [], Rhs, RIPosns, NewRhs ) :-
    adj_rhs_insts_(Rhs, RIPosns, [hard,out], NewRhs).
adj_rhs_insts_(Rhs, RIPosns, TypDir, NewRhs ) :-
    \+ var(NewRhs),
    wave_fronts( Rhs, [[]-RIPosns/TypDir], NNewRhs ),
    NewRhs = NNewRhs.
adj_rhs_insts_(Rhs, RIPosns, TypDir, NewRhs ) :-
    wave_fronts( Rhs, [[]-RIPosns/TypDir], NewRhs ).


smallest( BigT, S_Ts ) :-
    select( S-T, S_Ts, RestS_Ts ),
    \+ ( member( S1-_, RestS_Ts ), S > S1 ),
    !,
    ( T= BigT ; smallest( BigT, RestS_Ts ) ).







/* 
 * CLAM.v3.2
 *
 * This file contains code for the meta-level predicates
 * used to define the proof critics. The file is divided
 * preconditions and patches.
 * 
 */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRECONDITIONS
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% partially_blocked/2
%
%
/*
partially_blocked(Goal, WT):-
       matrix(_, Mat, Goal),
       partially_blocked_(Mat, WT).
partially_blocked_(Mat, WT):-
        member(Mat, [WT = R in _, WT => R]),
	fully_rippled(R),
        blocked_ripple(WT).        
partially_blocked_(Mat, WT):-
	member(Mat, [L = WT in _, L => WT]),
        fully_rippled(L),
        blocked_ripple(WT).
partially_blocked_(Mat, _):-
        member(Mat, [L = R in _, L => R]),
	((all_waves_sunk(L),
	  all_waves_beached(R));
	 (all_waves_sunk(R),
          all_waves_beached(L))).
*/
partially_blocked(Goal):-
       matrix(_, Mat, Goal),
       partially_blocked_(Mat).
partially_blocked_(Mat):-
        member(Mat, [L = R in _, L => R]),
	fully_rippled(R),
        blocked_ripple(L).        
partially_blocked_(Mat):-
	member(Mat, [L = R in _, L => R]),
        fully_rippled(L),
        blocked_ripple(R).
partially_blocked_(Mat):-
        member(Mat, [L = R in _, L => R]),
	((all_waves_sunk(L),
	  all_waves_beached(R));
	 (all_waves_sunk(R),
          all_waves_beached(L))).

% partial_blockage/3
%
%
partial_blockage(G, BTerm, equ(Typ)):-
        matrix(_, M, G),
	member(M, [RTerm = BTerm in Typ,
                   BTerm = RTerm in Typ,
                   RTerm => BTerm,
                   BTerm => RTerm]),
        (fully_rippled(RTerm);
         (all_waves_sunk(RTerm),
          all_waves_beached(BTerm))),!.

% fully_rippled/1
%
%
fully_rippled(Term):-
        all_waves_beached(Term),!.
fully_rippled(Term):-
        all_waves_sunk(Term),!.

% blocked_ripple/1
%
%
blocked_ripple(Term):-
    join_wave_fronts(Term, NTerm),
    wave_fronts(_, WSpec, NTerm),
    sinks(_, SSpec, NTerm),!,
    not forall {WPos\member(WPos-_, WSpec)}:
               ((WPos = []);
                (member(SPos, SSpec),
                 append(_, SPos, WPos))).

% all_waves_sunk/1
%
%
all_waves_sunk(Term):-
    join_wave_fronts(Term, NTerm),
    wave_fronts(_, WSpec, NTerm),
    sinks(_, SSpec, NTerm),
    \+ SSpec = [],
    \+ WSpec = [],
    forall {WPos\member(WPos-_, WSpec)}:
       (thereis {SPos\member(SPos, SSpec)}:
            append(_,SPos,WPos)).

% all_waves_beached/1
%
%
all_waves_beached(Term):-
    join_wave_fronts(Term, NTerm),
    wave_fronts(_, [[]-_/_], NTerm).
all_waves_beached(Term):-
    join_wave_fronts(Term, NTerm),
    wave_fronts(_, [], NTerm).

% casesplit_set/3
%
%
casesplit_set(Pat, _, [EWaveConds, ECompConds]):-
    condition_set(Pat, [WaveConds], [CompConds]),
    strip_meta_annotations(WaveConds, EWaveConds),
    strip_meta_annotations(CompConds, ECompConds).

% casesplit_set/2
%
%
casesplit_set(Pat, [WaveConds, CompConds]):-
    extract_conditions(Pat, WaveConds, CompConds).

% meta_ripple_pos/2
%
%
meta_ripple_pos(WaveTerm, NewWaveTerm):-
    wave_fronts(BareWaveTerm, WaveSpecs, WaveTerm),
    select(WFPos-WHPosL/[Typ,out], WaveSpecs, RestWaveSpecs),
    append([_], NewWFPos, WFPos),
    \+ member(NewWFPos-_, RestWaveSpecs),
    exp_at(BareWaveTerm, WFPos, BareWave), 
    exp_at(BareWaveTerm, NewWFPos, NewBareWave),
    functor(BareWave, Func, 1),
    functor(NewBareWave, Func, 1),
    wave_fronts(BareWaveTerm, [NewWFPos-WHPosL/[Typ,out]|RestWaveSpecs], NewWaveTerm).
meta_ripple_pos(WaveTerm, NewWaveTerm):-
    wave_fronts(BareWaveTerm, WaveSpecs, WaveTerm),
    select(WFPos-WHPosL/[Typ,in], WaveSpecs, RestWaveSpecs),
    append([1], WFPos, NewWFPos),
    \+ member(NewWFPos-_, RestWaveSpecs),
    exp_at(BareWaveTerm, WFPos, BareWave), 
    exp_at(BareWaveTerm, NewWFPos, NewBareWave),
    functor(BareWave, Func, 1),
    functor(NewBareWave, Func, 1),
    wave_fronts(BareWaveTerm, [NewWFPos-WHPosL/[Typ,in]|RestWaveSpecs], NewWaveTerm).

% meta_ripple_dir/2
%
%
meta_ripple_dir(Goal, Pos, NewWave):-
    matrix(_, Mat, Goal),
    reversible_wave_at(Mat, Pos, Wave),
    wave_fronts(Term, [WF-[WH]/[hard,out]], Wave),
    wave_fronts(Term, [WF-[WH]/[hard,in]], NewWave),
    sinkable(NewWave),
    wave_rule(Rn, _, _ => NewWave :=> _),
    current_goaltree(Plan),
    current_node(Plan, Addr),
    \+ ancestor_method(Plan, Addr, wave(_, [Rn, _])). 

reversible_wave_at(Wave = _ in _, [1,1], Wave):-
	fully_rippled(Wave).
reversible_wave_at(_ = Wave in _, [2,1], Wave):-
	fully_rippled(Wave).

partial_wave_rule_match(WaveTerm, NewWaveTerm):-
    wave_fronts(Term, WFSpec, WaveTerm),
    wave_fronts(Term, WFSpec, WaveTerm),
    WaveTerm =.. [WaveFunc|WaveArgs],
    skeleton_wave_args(WaveArgs, NewWaveArgs),
    wave_rule(_, _, _ => NewWaveTerm :=> _),
    wave_fronts(_, WFsBefore, NewWaveTerm),
    NewWaveTerm =.. [WaveFunc|NewWaveArgs],
    \+ NewWaveTerm = WaveTerm,
    wave_fronts(_, WFsBefore,NewWaveTerm),
    skeleton_term(NewWaveTerm, NTerm),
    skeleton_term(WaveTerm,    NTerm).

no_partial_wave_rule_match(WaveTerm):-
	\+ nested_wave_terms(WaveTerm),
        \+ partial_wave_rule_match(WaveTerm, _),
        \+ wave_fronts(_, [[_|_]-_/[hard,in]], WaveTerm).

skeleton_wave_args([], []).
skeleton_wave_args([Arg|Args], [NewArg|NewArgs]):-
	atomic(Arg),!,
        skeleton_wave_args(Args, NewArgs).
skeleton_wave_args([Arg|Args], [NewArg|NewArgs]):-
        wave_fronts(BareArg, [WPos-[WHPos]/TypDir], Arg), % Ensures no nested wave-terms
        append(WHPos, WPos, Pos),
        replace(Pos, MVar, BareArg, NewBareArg),
        wave_fronts(NewBareArg, [WPos-[]/TypDir], NewArg),
	skeleton_wave_args(Args, NewArgs).
        
nested_wave_terms(WaveTerm):-
	wave_fronts(_, [_,_|_], WaveTerm).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PATCHES
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% construct_lemma_lhs/2
% (calculation)
%
construct_lemma_lhs(_==>G, LHS, equ(Typ)):-
	matrix(_, Equ in Typ, G),
        construct_lemma_lhs_(Equ, LHS).
construct_lemma_lhs(_==>G, LHS, ConnTyp):-
        matrix(_, Imp, G),
        Imp = (_ => _),
        construct_lemma_lhs_(Imp, LHS),
        exp_at(Imp, Pos, LHS),
        strip_meta_annotations(Imp, BareImp),
        polarity(_, _, BareImp, Pos, Sign),
        construct_conntyp(Sign, _, ConnTyp).        

construct_lemma_lhs_(Form, L):-
        member(Form, [L = _, L => _]),
	blocked_ripple(L),!.
construct_lemma_lhs_(Form, R):-
        member(Form, [_ = R, _ => R]),
	blocked_ripple(R),!.
construct_lemma_lhs_(Form, L):-
        member(Form, [SL = _, SL => _]),
	all_waves_beached(SL),
	sinks(L, _, SL).
construct_lemma_lhs_(Form, R):-
        member(Form, [_ = SR, _ => SR]),
	all_waves_beached(SR),
	sinks(R, _, SR).

% construct_lemma_lhs/3
% (speculation)
%
construct_lemma_lhs(Context, NContext, Goal, Pos, LHS, equ(Typ)):-
        matrix(_, Mat, Goal),
        exp_at(Mat, Pos, SubMat),
        try_gen_skeleton(SubMat, Context, NContext, LHS),
        wave_fronts(BareTerm, _, LHS),
        guess_type(BareTerm, Typ),
        \+ Typ = u(1).
construct_lemma_lhs(Context, NContext, Goal, Pos, LHS, ConnTyp):-
	matrix(_, Mat, Goal),
        exp_at(Mat, Pos, SubMat),
        try_gen_skeleton(SubMat, Context, NContext, LHS),
        wave_fronts(BareTerm, _, LHS),
        guess_type(BareTerm, Typ),
        strip_meta_annotations(Mat, BareMat),
        polarity(_, _, BareMat, Pos, Sign),
        construct_conntyp(Sign, Typ, ConnTyp).

try_gen_skeleton(WT, Context, Context, WT):-
	wave_direction(WT, in).
try_gen_skeleton(WT, Context, [V:VTyp|Context], NewWT):-
        wave_direction(WT, out),
	wave_fronts(EWT, [WF-[WH]/_], WT),
	append(WH, WF, WHPos),
        exp_at(EWT, WHPos, WHTerm),
        guess_type(WHTerm, VTyp),
        freevarsinterm(EWT, Vars),
        hfree([V], Context),!,
	replace(WHPos, V, WT, NewWT).
	

construct_conntyp(+, u(1), imp_pos(u(1))).
construct_conntyp(-, u(1), imp_neg(u(1))).

size(X, 0):-
	var(X).
size(X, 1):-
        atomic(X).
size(X, N):-
        \+ atomic(X),
        X =.. [F|Args],
        size_list(Args, M),
        N is M + 1,!.
size_list([], 0).
size_list([H|T], N):-
        size(H, NH),
        size_list(T, NT),
        N is NH + NT.

% construct_lemma_rhs/2
% (calculation)
%
construct_lemma_rhs(H==>G, RHS, ConnTyp):-
        ConnTyp =.. [_,Typ],        
	matrix(_, Mat, G),
        member(Mat, [L = R in Typ, L => R]),
	all_waves_beached(L),
        blocked_ripple(R),!,
	induction_hyp(_:IndHyp, H),
	rewrite_beached_side(IndHyp, left, L, NewL),
        reverse_all_waves(NewL, RHS).
construct_lemma_rhs(H==>G, RHS, ConnTyp):-
        ConnTyp =.. [_,Typ],
	matrix(_, Mat, G),
        member(Mat, [L = R in Typ, L => R]),
	all_waves_beached(R),
	blocked_ripple(L),!,
	induction_hyp(_:IndHyp, H),
	rewrite_beached_side(IndHyp, right, R, NewR),
        reverse_all_waves(NewR, RHS).
construct_lemma_rhs(H==>G, RHS, ConnTyp):-
        ConnTyp =.. [_,Typ],
	matrix(_, Mat, G),
        member(Mat, [L = _ in Typ, L => _]),
	all_waves_sunk(L),!,
	induction_hyp(_:IndHyp, H),
	rewrite_sunk_side(IndHyp, left, L, NewL),
        reverse_all_waves(NewL, RHS).
construct_lemma_rhs(H==>G, RHS, ConnTyp):-
        ConnTyp =.. [_,Typ],
	matrix(_, Mat, G),
        member(Mat, [_ = R in Typ, _ => R]),
	all_waves_sunk(R),
	induction_hyp(_:IndHyp, H),
	rewrite_sunk_side(IndHyp, right, R, NewR),
        reverse_all_waves(NewR, RHS).

% construct_lemma_rhs/2
% (speculation)
%
construct_lemma_rhs(LHS, RHS, ConnTyp):-
        ConnTyp =.. [_,Typ],
        wave_fronts(BareTerm, _, LHS),
        guess_type(BareTerm, Typ),
	freevarsinterm(BareTerm, Context),
	construct_speculative_rhs(LHS, RHS, Context).

% construct_speculative_rhs/3
%
%
construct_speculative_rhs(LHS, RHS, Context):-
	construct_transverse_rhs(LHS, RHS, Context).
construct_speculative_rhs(LHS, RHS, Context):-
        construct_longitudinal_rhs(LHS, RHS, Context).

% construct_transverse_rhs/3
%
%
construct_transverse_rhs(LHS, RHS, Context):-
	wave_fronts(BareLHS, [WFPos-[WHPos]/[hard,out]], LHS),
	append(WHPos, WFPos, AbsWHPos),
	skeleton_term(LHS, SkelLHS),
        target_arg(BareLHS, TargetArg, TargetPos),
	\+ TargetPos = WFPos,
        sinks(_, [_|_], TargetArg),
        construct_speculative_term(TargetArg, Context, PWFront),
        replace(TargetPos, PWFront, SkelLHS, RHS).

% construct_longitudinal_rhs/3
%
%
construct_longitudinal_rhs(LHS, RHS, Context):-
	wave_fronts(_, [_-_/[hard,out]], LHS),
	skeleton_term(LHS, SkelLHS),
        construct_speculative_term(SkelLHS, Context, RHS).
construct_longitudinal_rhs(LHS, RHS, Context):-
	wave_fronts(_, [_-_/[hard,in]], LHS),
	skeleton_term(LHS, SkelLHS),
        sinks(_, [SPos], SkelLHS),
        append(_, [APos], SPos),
        exp_at(SkelLHS, [APos], Arg),
        construct_speculative_term(Arg, Context, PArg),
        replace([APos], PArg, SkelLHS, RHS).

% rewrite_beached_side/4
%
%
rewrite_beached_side(Hyp, left, WTerm, NewWTerm):-
	matrix(_, Mat, Hyp),
        member(Mat, [L = R in _, L => R]),
        join_wave_fronts(WTerm, NWTerm),
	((wave_fronts(_, [[]-[Pos]/_], NWTerm),
	  replace(Pos, R, NWTerm, NewWTerm));
         (NewWTerm = R)),!.
rewrite_beached_side(Hyp, right, WTerm, NewWTerm):-
	matrix(_, Mat, Hyp),
        member(Mat, [L = R in _, L => R]),
        join_wave_fronts(WTerm, NWTerm),
	((wave_fronts(_, [[]-[Pos]/_], NWTerm),
	  replace(Pos, L, NWTerm, NewWTerm));
         (NewWTerm = L)),!.

% join_wave_fronts/2
%
%
join_wave_fronts(Term, NTerm):-
	join_wave_fronts(Term, _, NTerm).
join_wave_fronts(Term, Term).

% rewrite_sunk_side/4
%
%
rewrite_sunk_side(Hyp, left, WTerm, NewWTerm):-
	matrix(Vars, Mat, Hyp),
        member(Mat, [L = R in _, L => R]),
	replace_universal_vars(Vars, [L,R], [WTerm,NWTerm]),
        sinks(NewWTerm, _, NWTerm).
rewrite_sunk_side(Hyp, right, WTerm, NewWTerm):-
	matrix(Vars, Mat, Hyp),
        member(Mat, [L = R in _, L => R]),
	replace_universal_vars(Vars, [L,R], [NWTerm,WTerm]),
        sinks(NewWTerm, _, NWTerm).


% reverse_all_waves/2
%
%
reverse_all_waves(Term, NewTerm):-
    wave_fronts(RawTerm, WFSpec, Term),
    rev_waves(WFSpec, NewWFSpec),
    wave_fronts(RawTerm, NewWFSpec, NewTerm).

% rev_waves/2 
%
%
rev_waves([], []).
rev_waves([WF-WHs/[Typ,Dir]|Rest], [WF-WHs/[Typ,RDir]|RRest]):-
    toggle_dir(Dir, RDir),
    rev_waves(Rest, RRest).

% toggle_dir/2
%
toggle_dir(in, out).
toggle_dir(out, in).

% construct_lemma_condition/3
%
%
construct_lemma_condition(H, Form, [Cond]):-
        strip_meta_annotations(Form, EForm),
	freevarsinterm(EForm, VarsEForm),
	setof(Cond, (member(_:Cond, H),
	             member(Cond, [(_=_ in _), (_ < _), (_ => void)])),
              Conds),
        member(Cond, Conds),
	freevarsinterm(Cond, VarsCond),
	subseq(VarsEForm, VarsCond, _).
construct_lemma_condition(_, _, []).
    


% construct_generalized_lemma/5
%
%
construct_generalized_lemma(LHS, RHS, Typ, Context, Name:([]==>Lemma)):-
    construct_lemma(LHS, RHS, Typ, Context, Lemma1),
    generalize(Lemma1, Lemma2),
    ripple_and_cancel(Lemma2, Lemma),
    \+ known_lemma(Lemma),
    \+ trivial_lemma(Lemma),
    \+ disprove([]==>Lemma),
    tag_with_number(lemma, lemma_cnt, Name),!.

% known_lemma(Lemma):-
%       matrix(_, Mat, Lemma),
%       contains_meta_variables(Mat),!.
known_lemma(Lemma):-
        theorem(_, Lemma, thm).

trivial_lemma(Lemma):-
	matrix(_, Term = Term in _, Lemma).
/*
trivial_lemma(Lemma):-
	matrix(Vars, LHS = RHS in Typ, Lemma),
        exp_at(RHS, Pos, SubRHS),
        SubRHS =.. [MVar,Arg|_],
        is_meta_variable(MVar),
        replace(Pos, Arg, RHS, NRHS),
        matrix(Vars, Term = NRHS in Typ, NLemma),
        trivial_lemma(NLemma).
*/

% construct_lemma/5
%
% Non-conditional lemmata are generated first. 
%
construct_lemma(LHS, RHS, ConnTyp, Context, Lemma):- 
    strip_meta_annotations(LHS-RHS, L-R),
    freevarsinterm(L-R, Vs),
    map_list(Vs, V :=> (V:T), member(V:T, Context), VTsLemma),
    construct_form(L, RHS, ConnTyp, Form),
    matrix(VTsLemma, Form, Lemma). % RHS annotated for rippling-in
construct_lemma(LHS, RHS, ConnTyp, Context, Lemma):-
    construct_lemma_condition(Context, LHS, [Cond]),
    strip_meta_annotations(LHS-RHS, L-R),
    freevarsinterm(L-R, Vs),
    map_list(Vs, V :=> (V:T), member(V:T, Context), VTsLemma),
    construct_form(L, RHS, ConnTyp, Form),
    matrix(VTsLemma, Cond => Form, Lemma). % RHS annotated for rippling-in
 
construct_form(L, RHS, imp_pos(_), RHS => L).
construct_form(L, RHS, imp_neg(_), L => RHS).
construct_form(L, RHS, equ(Typ), L = RHS in Typ).

% ripple_and_cancel/2
%
%
ripple_and_cancel(G, NewG):-
    wave_occ_at(G, Pos, L),
    wave_rule(_, _, C=>L:=>R),
    % Ensure that only non-speculative wave-rules
    % are used for rippling-in.
    \+ contains_meta_variables(R), 
    elementary([]==>C, _),
    replace_in_matrix(Pos, R, G, G1),
    cancel(G1, G2),
    \+ disprove([]==>G2),
    strip_meta_annotations(G2, NewG).
ripple_and_cancel(G, NewG):-
    cancel(G, G1),
    strip_meta_annotations(G1, NewG).
ripple_and_cancel(G, NewG):-
    strip_meta_annotations(G, NewG).

% cancel/2
%
%
cancel(G, NewG):-
    strip_meta_annotations(G, G1),
    matrix(Vars, L = R in _, G1),
    cancel_functors(L, R, NL, NR),
    L \== NL,
    guess_type(NL, Typ),
    matrix(Vars, NL = NR in Typ, NewG).

% cancel_functors/4
%
%
cancel_functors(L,R, NL, NR):-
    L =.. [F,ArgL],
    R =.. [F,ArgR],
    cancel_functors(ArgL, ArgR, NL, NR).
cancel_functors(L,R, NL, NR):-
    L =.. [F,Arg1,Arg2],
    R =.. [F,Arg3,Arg2],
    cancel_functors(Arg1, Arg3, NL, NR).
cancel_functors(L,R, L, R).
    

% tag_with_number/3
%
%
tag_with_number(Name, CntRef, NameN):-
    recorded(CntRef,N,_),
    name(Name, StrName),
    name(N, StrN),
    append(StrName, StrN, StrNameN),
    name(NameN, StrNameN),
    M is N+1,
    uniq_recorda(CntRef,M,_).

% generalize/2
%
%
generalize(Lemma, GenLemma):-
    generalize_all_common_subterms(Lemma, Lemma, GenLemma).
generalize(Lemma, GenLemma):-
    generalize_common_subterms(Lemma, GenLemma).
generalize(Lemma, GenLemma):-
    generalize_vars_apart(Lemma, GenLemma).
generalize(Lemma, Lemma).

% generalize_all_common_subterms/2
%
% replacement of common subterms
%
generalize_all_common_subterms(Lemma, OrigLemma, GenLemma):-
	generalize_common_subterms(Lemma, GenLemma1),
	generalize_all_common_subterms(GenLemma1, OrigLemma, GenLemma).
generalize_all_common_subterms(GenLemma, OrigLemma, GenLemma):-
	\+ GenLemma = OrigLemma.

% generalize_common_subterms/2
%
% replacement of common subterms
%
generalize_common_subterms(Lemma, GenLemma):- 
    precon_matrix(VarTyps, Cond => LHS = RHS in Typ, Lemma),
    generalize_common_subterms_(VarTyps, LHS, RHS, NewVarTyps, NewLHS, NewRHS),
    precon_matrix(NewVarTyps, Cond => NewLHS = NewRHS in Typ, GenLemma).
generalize_common_subterms(Lemma, GenLemma):- 
    precon_matrix(VarTyps, Cond => LHS => RHS, Lemma),
    generalize_common_subterms_(VarTyps, LHS, RHS, NewVarTyps, NewLHS, NewRHS),
    precon_matrix(NewVarTyps, Cond => NewLHS => NewRHS, GenLemma).

generalize_common_subterms_(VarTyps, LHS, RHS, NewVarTyps, NewLHS, NewRHS):-
    exp_at(LHS, _, Exp),
    not atom(Exp),           % disallow generalising object-level variables
    not constant(Exp, _),    % Exp must not be a constant term.
    object_level_term(Exp),  % Exp must not contain meta-vars or wave fronts
    exp_at(RHS, _, Exp),
    hfree([Var], VarTyps),
    guess_type(Exp, ExpTyp),
    append([Var:ExpTyp], VarTyps, ExtVarTyps),
    replace_all(Exp, Var, LHS-RHS, NewLHS-NRHS),
    add_to_meta_term_context(NewLHS, NRHS, NewRHS),
    freevarsinterm(NewLHS-NewRHS, FreeVars),
    listof(V:T, (member(V, FreeVars), member(V:T, ExtVarTyps)), NewVarTyps).

% distinguishing-variables-apart/2
%
% distinguishing-variables-apart
%
generalize_vars_apart(Lemma, GenLemma):-
    precon_matrix(VarTyps, Cond => LHS = RHS in Typ, Lemma),
    member(Var:VarTyp, VarTyps),
    (non_wave_occ(LHS, [Var], [NPosL], _, _),
     non_wave_occ(RHS, [Var], [NPosR], _, _)),
    wave_occ(LHS, [Var], [PosL], _, _, Sch, _),
    wave_occ(RHS, [Var], [PosR], _, _, Sch, _),
    \+ NPosL = PosL,
    \+ NPosR = PosR,
    hfree([NewVar], VarTyps),
    append([NewVar:VarTyp], VarTyps, ExtVarTyps),
    replace(PosL, NewVar, LHS, NewLHS),
    replace(PosR, NewVar, RHS, NRHS),
    add_to_meta_term_context(NewLHS, NRHS, NewRHS),
    precon_matrix(ExtVarTyps, Cond => NewLHS = NewRHS in Typ, GenLemma).

add_to_meta_term_context(_, RHS, RHS):-
	\+ contains_meta_variables(RHS),!.
add_to_meta_term_context(LHS, RHS, NewRHS):-
        freevarsinterm(LHS, VarsLHS),
	meta_term_occ_at(RHS, Pos, MetaTerm),
        MetaTerm =.. [MetaFunc,MetaArg|_],
        union([MetaArg], VarsLHS, NewVars),
        NewMetaTerm =.. [MetaFunc|NewVars],
        add_def(NewMetaTerm <==> void),
        replace(Pos, NewMetaTerm, RHS, NewRHS),!.

% validate_calculation/2
%
%
validate_calculation(Plan, Name:Lemma):-
        print_conjecture(Lemma, Name),
	add_thm(Name, Lemma),
	record_thm(Name, thm),
        ThmName =.. [thm, Name],
        lib_dir(LibDir),
        lib_save(ThmName, LibDir),	
	plan(Plan, Name, dplan),
        add_wave_rules(Name, _).

% validate_speculation/2
%
%
validate_speculation(Plan, Name:LemmaSpec):-
        print_conjecture(LemmaSpec, Name),
        add_theorem(Name, LemmaSpec),
        add_wave_rules(Name, _),
        current_node(Plan, Addr),
        chop_branch(Plan, Addr),
        plan(Plan, Plan, dplan),
        apply_results(Plan, LemmaSpec, Lemma, Name).


apply_results(_, _, _, Name):-
        goaltree_status(Name, complete),!.       % Hack: due to mix between
apply_results(Plan, LemmaSpec, Lemma, Name):-    % explicit plan state and
        extract_subst_list(Plan, SubstL),        % use of recursion.
	apply_subst_list(SubstL, LemmaSpec, Lemma),
        add_theorem(Name, Lemma),
        plan(Plan, Name, dplan),  
        apply_subst_to_goaltree(Plan, SubstL),
        add_wave_rules(Name, _).


% add_theorem/2
%
%
add_theorem(Name, Lemma):-
        add_thm(Name, Lemma),
        record_thm(Name, thm),
        ThmName =.. [thm, Name],
        % lib_dir(LibDir),
        saving_dir(LibDir),
        lib_save(ThmName, LibDir).

% original_lemma/1
%
%
original_lemma([]==>Lemma):-
	\+ theorem(_, Lemma, thm).

target_arg(Term, Arg, [Pos]):-
	functor(Term, _, ArgCnt),
        target_arg_(Term, Arg, ArgCnt, Pos).
target_arg_(_, _, 0, _):- !,fail.
target_arg_(Term, Arg, Pos, Pos):-
	arg(Pos, Term, Arg).
target_arg_(Term, Arg, Pos, ArgPos):-
	NPos is Pos - 1,
	target_arg_(Term, Arg, NPos, ArgPos).

% construct_speculative_term/3
%
%        
construct_speculative_term(Term, Context, NewTerm):-
        sinks(NTerm, _, Term),
        subtract(Context, [NTerm], NContext),
	generate_meta_variable(HOVar),
        append([NTerm], NContext, Args),
	NewTerm =.. [HOVar|Args],
        add_def(NewTerm <==> void),!. % Oyster dependency :-(
        
skeleton_term(WTerm, STerm):-
	skeleton_term_(WTerm, out, STerm).
skeleton_term_(Term, out, Term):-
	(atomic(Term);var(Term)),!.
skeleton_term_('@wave_front@'(_, _, WTerm), out, STerm):-
	skeleton_term_(WTerm, in, STerm),!.
skeleton_term_('@wave_var@'(WTerm), in, STerm):-
	skeleton_term_(WTerm, out, STerm),!.
skeleton_term_(WTerm, out, STerm):-
	WTerm =.. [F|WArgs],
        skeleton_term_list(WArgs, out, SArgs),
        STerm =.. [F|SArgs].
skeleton_term_(WTerm, in, STerm):-
        WTerm =.. [F|WArgs],
        skeleton_term_list(WArgs, in, [STerm]).
skeleton_term_list([], _, []).
skeleton_term_list([WT|WTs], Status, [ST|STs]):-
	skeleton_term_(WT, Status, ST),!,
	skeleton_term_list(WTs, Status, STs).
skeleton_term_list([_|WTs], Status, STs):-
	skeleton_term_list(WTs, Status, STs).
        	

% construct_context/3
%
%
construct_context(Hyps, Goal, Context):-
	matrix(VarTyps, Mat, Goal),
        append(VarTyps, Hyps, Context).

/*
construct_context(Hyps, Goal, Context):-
	matrix(VarTyps, Mat, Goal),
        append(VarTyps, Hyps, AllHyps),
        strip_meta_annotations(Mat, NMat),
	freevarsinterm(NMat, FreeVars),
	map_list(FreeVars, V:=> (V:T), member(V:T, AllHyps), Context).
*/

% store_wave_rules/1
%
%
store_wave_rules(Name:Lemma):-
    add_thm(Name, Lemma),
    record_thm(Name, thm),
    add_wave_rules(Name,_).


% standardize_vars_apart/2
%
%
standardize_vars_apart(T, T):-
    oyster_type(_, _, [T]),!.
standardize_vars_apart(T, NT):-
    atom(T),!,is_grounded(NT).
standardize_vars_apart(T, NT):-
    T =.. [F|Args],
    standardize_vars_list_apart(Args, NArgs),
    NT =.. [F|NArgs].

standardize_vars_list_apart([], []).
standardize_vars_list_apart([H|T], [NH|NT]):-
    standardize_vars_apart(H, NH),
    standardize_vars_list_apart(T, NT).

% construct_generalisation/3
%
%
construct_generalisation(Context, G, Name:([]==>Lemma)):-
	matrix(_, L = R in Typ, G),
        hfree([Var], Context),
        construct_generalisation(L, R, Var, GenL, GenR),
	construct_lemma(GenL, GenR, equ(Typ), [Var:Typ|Context], Lemma),
        tag_with_number(lemma, lemma_cnt, Name).

% construct_generalisation/5
%
%
construct_generalisation(L, R, Var, GenL, GenR):-
	construct_gen_terms(L, Var, GenL),
	construct_gen_terms(R, Var, GenR).

% construct_gen_terms/3
%
%
construct_gen_terms(Term, Var, NewTerm):-  % blocked transverse ripple
        wave_fronts(_, WSpec, Term),
        \+ member([]-_, WSpec), 
        exp_at(Term, Pos, LHS),
        wave_rule(_, trans(_), _ => LHS :=> RHS),
	wave_fronts(_, [WPosRHS-_], RHS),
        append(WPosRHS, Pos, SPos),
        construct_gen_term(Term, Var, SPos, NTerm),
        strip_meta_annotations(NTerm, NewTerm).
construct_gen_terms(Term, Var, NewTerm):-  % potential transverse ripple
        wave_fronts(_, WSpec, Term),
        member([]-_, WSpec),
        construct_gen_term(Term, Var, [], NTerm),
        strip_meta_annotations(NTerm, NewTerm).

% construct_gen_term/4
%
%
construct_gen_term(Term, Var, [], SpecTerm):- !,
        skeleton_term(Term, SkelTerm),
        construct_speculative_term(SkelTerm, [Var], SpecTerm).
construct_gen_term(Term, Var, Pos, SpecTerm):-
        skeleton_term(Term, SkelTerm),
        exp_at(SkelTerm, Pos, SubTerm),
        oyster_type(_, _, [SubTerm]),!,    % Hack!!
        construct_speculative_term(Var, [], NewSubTerm),
	replace(Pos, NewSubTerm, SkelTerm, SpecTerm).
/*
construct_gen_term(Term, Var, Pos, SpecTerm):-
        exp_at(Term, Pos, SubTerm),
        skeleton_term(Term, SkelTerm),
        SubTerm =.. [Func, Arg],!,
        construct_speculative_term(Var, [], SinkTerm),
        NewSubTerm =.. [Func,SinkTerm],
        replace(Pos, NewSubTerm, SkelTerm, SpecTerm).
 */
construct_gen_term(Term, Var, Pos, SpecTerm):-
        skeleton_term(Term, SkelTerm),
        exp_at(SkelTerm, Pos, SubTerm),
        construct_speculative_term(SubTerm, [Var], NewSubTerm),
        replace(Pos, NewSubTerm, SkelTerm, SpecTerm).


        % refine_induction/3
        %
        %
refine_induction(H, WaveTerm, NewSch, Var:Typ):-
    reverse_all_waves(WaveTerm, RWaveTerm),
    ripple_in(H, RWaveTerm, RippledRWaveTerm),
    join_wave_fronts(RippledRWaveTerm, _, JoinedRippledRWaveTerm),
    wave_fronts(UnAnnTerm, [WFPos-[WHPos]/_|_], JoinedRippledRWaveTerm),  %% Generalise 
    exp_at(UnAnnTerm, WFPos, NewSch),
    append(WHPos, WFPos, AbsWHPos),
    exp_at(UnAnnTerm, AbsWHPos, Var),
    member(Var:Typ, H).

ripple_in(H, G, NewG):-
    wave_occ_at(G, Pos, L),
    wave_rule(Rn, _, C=>L:=>R),
    theorem(Rn, _, eqn),     % Hack to prevent lemmata being used. Should
    elementary(H==>C, _),    % really check that ripple-in actually enables
                             % an induction, see halflenapp example
                             % where rippling-in (via lemma1) gives _::v0::nil
                             % as the revised induction scheme.
    replace_in_matrix(Pos, R, G, G1),
    ripple_in(H, G1, NewG).
ripple_in(H, G, NewG):-
    split_wave_fronts(G, _, NG),
    ripple_in(H, NG, NewG).
ripple_in(H, G, NewG):-
    single_wave_occ_at(G, Pos, WaveTerm),
    meta_ripple_wave(WaveTerm, NewWaveTerm, _),
    replace(Pos, NewWaveTerm, G, NG),
    ripple_in(H, NG, NewG).
ripple_in(_, G, G).


        % construct_subcases/
        %
        %
construct_case_goals(H, G, Cases, Pos, SubGs):-
	matrix(Vars, Matrix, G),
	listof(Var:Typ, (member(Var:Typ,Vars),
                         not freevarincondition(Cases,Var)),
               NewVars1),
        listof(Var:Typ, (member(Var:Typ,Vars),
                         freevarincondition(Cases, Var)),
               NewVars2),
        matrix(NewVars1, Matrix, NewMatrix),
        append(NewVars2, H, NewH),
        split_into_cases(Cases, Pos, NewH==>NewMatrix, SubGs).

        % split_into_cases/4
        %
        %
split_into_cases([WaveConds,CompConds], Pos, Sequent, NewSequents):-
        split_into_ripple_cases(WaveConds, Pos, Sequent, Sequents1),
        split_into_nonripple_cases(CompConds, Pos, Sequent, Sequents2),
        append(Sequents1, Sequents2, NewSequents).

split_into_nonripple_cases([], _, _, []).
split_into_nonripple_cases([Cond|Conds], Pos, H==>G, [NH==>NG|Sequents]):-
        matrix(Vs, M, G),
	extend_hyps_with_cond(Cond, Vs, H, NH),
	exp_at(M, Pos, Exp),
        strip_meta_annotations(Exp, NExp),
        replace(Pos, NExp, M, NM),
        matrix(Vs, NM, NG),
        split_into_nonripple_cases(Conds, Pos, H==>G, Sequents).

split_into_ripple_cases([], _, _, []).
split_into_ripple_cases([Cond|Conds], _, H==>G, [NH==>G|Sequents]):-
        matrix(Vs, M, G),
	extend_hyps_with_cond(Cond, Vs, H, NH),
	split_into_ripple_cases(Conds, _, H==>G, Sequents).
        
freevarincondition([C1, C2], V):-
        append(C1, C2, C3),
	freevarinterm(C3, V).


%
% casesplit_set_implicit/2
%
%
casesplit_set_implicit(Pat, Context, Cases):-
    \+ atomic(Pat),
    freevarsinterm(Pat, Vars),
    member(Var, Vars),
    member(Var:Typ, Context),
    check_coverage(Pat, Var, Typ),
    type_to_casesplit(Var:Typ, Cases),!.

check_coverage(Pat, Var, Typ):-
    canonical_constructors(Typ, CList),
    forall{C\CList}:(replace_all(Var, C, Pat, NewPat),
                     func_defeqn(NewPat, _)).

canonical_constructors(pnat, [0,s(_)]).
canonical_constructors(pnat list, [nil,_::_]).

type_to_casesplit(Var:pnat, [[Var = 0 in pnat],
                             [Var = 0 in pnat => void,
                              Var = s(pred(Var)) in pnat]]).
type_to_casesplit(Var:pnat list, [[Var = nil in pnat list],
                                  [Var = hd(Var)::tl(Var) in pnat list,
                                   Var = nil in pnat list => void]]).


    
    
    
    

/*
 * CLAM.v3.2
 *
 * This file contains code for the wave-rule-matcher
 * together with predicates to interface with img's
 * higher-order unification predicates.
 *
 */

% wave_rule_match/4
%
% rippling in the presence of definite wave-function
% and wave-front. 
wave_rule_match(RuleName, long(Dir), C=>L:=>R, []):-
    \+ var(L),
    wave_rule(RuleName, long(Dir), C=>L:=>R),
    ((wave_direction(R, in), sinkable(R));  % ensure that in-bound waves
      wave_direction(R, out);               % are making progress to sinks.
      wave_fronts(_, [], R)).

wave_rule_match(RuleName, trans(Dir), C=>L:=>R, []):-
    \+ var(L),
    wave_rule(RuleName, trans(Dir), C=>L:=>R).
%
% rippling in the presence of definite wave-function
% and potential wave-front.
wave_rule_match(RuleName, TypeDir, C=>L:=>R, SubstL):-
    \+ var(L),
    potential_wave_occ(L),
    definite_wave_func(L),
    wave_rule(RuleName, TypeDir, C=>LHS:=>R),
    unify_ho_pterms(L, LHS, R, SubstL),!.
%
% rippling in the presence of potential wave-function
% and definite wave-front.
wave_rule_match(RuleName, TypeDir, C=>L:=>R, [[SubstL,SubstR]]):-
    \+ var(L),
    definite_wave_occ(L),
    potential_wave_func(L),
    wave_rule(RuleName, TypeDir, C=>LHS:=>R),
    compatible_wave_terms(L, LHS, out, _),
    copy(LHS, CLHS),
    match_waves(L, CLHS),
    match_waves(L,LHS),
    wave_fronts(EraseL, _, L),
    skeleton_term(L, SkelL),
    skeleton_term(LHS, SkelLHS),
    strip_meta_annotations(CLHS, EraseCLHS),
    skeleton_term(CLHS, SkelCLHS),
    freevarsinterm(SkelL, FVars),
    hou_pterms(FVars, Subs, SkelL, SkelCLHS),
    apply_subs_to_pterm(Subs, SkelL, NewSkelL),
    SkelLHS = NewSkelL,
    SkelL =.. [F|Args],
    same_length(Args, MArgs),
    SubstL =.. [F|MArgs],
    zip(ArgsMArgs, Args, MArgs),
    replace_all(ArgsMArgs, NewSkelL, SubstR),
    sinks_preserved(L, R).

wave_rule_match(RuleName, TypeDir, C=>L:=>R, [[SubstL,SubstR]]):-
    \+ var(L),
    definite_wave_occ(L), 
    potential_wave_func(L),
    wave_rule(RuleName, TypeDir, C=>LHS:=>R),
    compatible_wave_terms(L, LHS, in, _),
    match_wave_fronts(L, LHS),
    wave_fronts(EraseL, [WFL-[WHL]/_], L),
    wave_fronts(EraseLHS, [WFLHS-[WHLHS]/_], LHS),
    append(WHL, WFL, AbsWHL),
    append(WHLHS, WFLHS, AbsWHLHS),
    exp_at(EraseL, AbsWHL, WaveHoleL),
    exp_at(EraseLHS, AbsWHLHS, WaveHoleLHS),
    copy(WaveHoleLHS, CWaveHoleLHS),
    freevarsinterm(WaveHoleL, FVars),
    hou_pterms(FVars, Subs, WaveHoleL, CWaveHoleLHS),
    apply_subs_to_pterm(Subs, WaveHoleL, NewWaveHoleL),
    NewWaveHoleL = WaveHoleLHS,
    WaveHoleL =.. [F|Args],
    same_length(Args, MArgs),
    SubstL =.. [F|MArgs],
    zip(ArgsMArgs, Args, MArgs),
    replace_all(ArgsMArgs, NewWaveHoleL, SubstR),
    sinks_preserved(L, R).

sinks_preserved(T1, T2):-
	sinks(_, [], T1),
        sinks(_, [], T2).
sinks_preserved(T1, T2):-
	sinks(_, [_|_], T1),
        sinks(_, [_|_], T2).

replace_all([], Term, Term).
replace_all([X-Y|Rest], Term, NewTerm):-
	replace_all(X, Y, Term, NTerm),
	replace_all(Rest, NTerm, NewTerm).


% unify_ho_pterms/4
%
% out-bound waves 
%
unify_ho_pterms(Term, LHS, RHS, SubstL):- 
        compatible_wave_terms(Term, LHS, out, _),
        copy(LHS, CLHS),
        strip_meta_annotations(Term, EraseTerm),
	strip_meta_annotations(LHS,  EraseLHS),
	strip_meta_annotations(CLHS, EraseCLHS),
	freevarsinterm(EraseTerm, FVars),
        hou_pterms(FVars, Subs, EraseTerm, EraseCLHS),
        generate_annsubst_list(Term, LHS, Subs, SubstL1),
        coerce_partial_lemma(SubstL1, SubstL),
        apply_annsubst_list(SubstL, Term, LHS),
        \+ meta_petering_out(LHS, RHS),!.
%
% in-bound waves
%
unify_ho_pterms(Term, LHS, RHS, SubstL):-
        compatible_wave_terms(Term, LHS, in, _),
        copy(LHS, CLHS),
        copy(Term, CTerm), % Term will contain a prolog variable
                           % if it contains a soft wave-front. 
        match_wave_holes(CTerm, CLHS),
        strip_meta_annotations(Term, EraseTerm),
	strip_meta_annotations(LHS,  EraseLHS),
        strip_meta_annotations(CLHS, EraseCLHS),
	freevarsinterm(EraseTerm, FVars),
        hou_pterms(FVars, Subs, EraseTerm, EraseCLHS),
        generate_annsubst_list(Term, LHS, Subs, SubstL1),
        coerce_partial_lemma(SubstL1, SubstL),
        apply_annsubst_list(SubstL, Term, LHS),
        \+ meta_petering_out(LHS, RHS),!.

% meta_petering_out/1
% 
%
meta_petering_out(LHS, RHS):-
	cnt_meta_variables(LHS, N),
        cnt_meta_variables(RHS, M),
        M < N.

cnt_meta_variables(Term, N):-
        findall(MVar, (exp_at(Term,_,MVar),is_meta_variable(MVar)), MVarL),
        length(MVarL, N),!.

% compatible_wave_terms/4
% 
%
compatible_wave_terms(Term1, Term2, Dir, WaveFunc):-
        wave_function(Term1, WaveFunc1),
	wave_function(Term2, WaveFunc2),
        compatible_wave_funcs(WaveFunc1, WaveFunc2),
	wave_direction(Term1, Dir),
	wave_direction(Term2, Dir).

compatible_wave_funcs(Func, Func).
compatible_wave_funcs(Func, _):-
	is_meta_variable(Func).
compatible_wave_funcs(_, Func):-
	is_meta_variable(Func).

        
% wave_direction/2
%
%
wave_direction(Wave, Dir):-
    wave_fronts(_, [_-_/[_,Dir]|_], Wave).

% definite_wave_occ/1
%
%
definite_wave_occ(Exp):-
    wave_fronts(_, WFSpec, Exp),
    member(_-_/[Type,in], WFSpec),
    \+ var(Type).
definite_wave_occ(Exp):-
    wave_fronts(_, WFSpec, Exp),
    member(_-_/[Type,out], WFSpec),
    \+ var(Type).


% generate_annsubst_list/4
%
% out-bound case
%
generate_annsubst_list(Term, LHS, Subs, [Subst]):-
    wave_fronts(ETerm, WFSpec1, Term),
    wave_fronts(ELHS,  WFSpec2, LHS),
    member(WFPos1-[WHPos1]/[Type1,Dir1], WFSpec1),
    member(WFPos2-[WHPos2]/[Type2,Dir2], WFSpec2),
    Dir1 = out,
    Dir2 = out,
    var(Type1),
    exp_at(ETerm, WFPos1, MTerm),
    MTerm =.. [F|Args],
    same_length(Args, MArgs),
    map_list(MArgs, L:=>GL-L, is_grounded(GL), GMArgsL),
    zip(GMArgsL, GArgs, MArgs),
    GTerm =.. [F|GArgs],
    apply_subs_to_pterm(Subs, GTerm, NGTerm),
    wave_fronts(GTerm,  [[]-[WHPos1]/[Type1,Dir1]], AnnGTerm),
    wave_fronts(NGTerm, [[]-[WHPos2]/[Type2,Dir2],
                         WHPos2-[WHPos1]/[Type1,Dir1]], AnnNGTerm),
    replace_universal_vars_1(GMArgsL, [AnnGTerm, AnnNGTerm], Subst),!.
%
% in-bound case
%
generate_annsubst_list(Term, LHS, Subs, [Subst]):-
    wave_fronts(ETerm, WFSpec1, Term),
    wave_fronts(ELHS,  WFSpec2, LHS),
    member(WFPos1-[WHPos1]/[Type1,Dir1], WFSpec1),
    member(WFPos2-[WHPos2]/[Type2,Dir2], WFSpec2),
    Dir1 = in,
    Dir2 = in,
    var(Type1),
    exp_at(ETerm, WFPos1, MTerm),
    MTerm =.. [F|Args],
    same_length(Args, MArgs),
    map_list(MArgs, L:=>GL-L, is_grounded(GL), GMArgsL),
    zip(GMArgsL, GArgs, MArgs),
    GTerm =.. [F|GArgs],
    apply_subs_to_pterm(Subs, GTerm, NGTerm1),
    % Replace meta-term in wave-hole with WaveVar: this problem
    % due to the fact that unification is top-down while rippling-in
    % requires bottom-up unification process.
    exp_at(GTerm, WHPos1, WaveVar),
    replace(WHPos2, WaveVar, NGTerm1, NGTerm),
    wave_fronts(GTerm,  [[]-[WHPos1]/[Type1,Dir1]], AnnGTerm),
    wave_fronts(NGTerm, [[]-[WHPos2]/[Type2,Dir2]], AnnNGTerm1),
    add_trailing_pwave(Term, AnnNGTerm1, AnnNGTerm),
    replace_universal_vars_1(GMArgsL, [AnnGTerm, AnnNGTerm], Subst),!.

% add_trailing_pwave/3
%
%
add_trailing_pwave(MTerm, WTerm, NewWTerm):-
	wave_fronts(EMTerm1, [WFPos-[WHPos]/[_,in]], MTerm),
	append(WHPos, WFPos, AbsWHPos),
	replace(AbsWHPos, WTerm, EMTerm1, EMTerm2),
	EMTerm2 =.. [_|Args],
	generate_meta_variable(MVar),
	EMTerm3 =.. [MVar|Args],
        wave_fronts(EMTerm3, [WFPos-[WHPos]/[_,in]], NewWTerm).

% potential_wave_occ/1
%
%
potential_wave_occ(Exp):-
    wave_fronts(_, WFSpec, Exp),
    member(_-_/[Type,_], WFSpec),
    var(Type).

% definite_wave_func/1
%
%
definite_wave_func(Exp):-
    wave_function(Exp, Func),
    \+ is_meta_variable(Func).

% potential_wave_func/1
%
%
potential_wave_func(Exp):-
    wave_function(Exp, Func),
    is_meta_variable(Func).

% wave_function/2
%
%
wave_function(WaveTerm, WaveFunc):-
    wave_fronts(_, [[_|WF]-WHs/[_,out]|_], WaveTerm),
    exp_at(WaveTerm, WF, WaveOcc),
    functor(WaveOcc, WaveFunc, _).
wave_function(WaveTerm, WaveFunc):-
    wave_fronts(_, [WF-[WH]/[_,in]|_], WaveTerm),
    append(WH, WF, AbsWH),
    exp_at(WaveTerm, AbsWH, HoleOcc),
    \+ var(HoleOcc),
    HoleOcc =.. [WaveFunc|_].

% is_meta_term/1
%
%
is_meta_term(Term):-
        \+ var(Term),
        functor(Term, Func, _),
        is_meta_variable(Func).

% meta_term_occ_at/3
%
%
meta_term_occ_at(Form, Pos, Term):-
        exp_at(Form, Pos, Term),
        \+ atomic(Term),
        is_meta_term(Term).

% meta_variable_occ_at/3
%
%
meta_variable_occ_at(Term, Pos, MVar):-
	exp_at(Term, Pos, MVar),
	is_meta_variable(MVar).

meta_variable_occ_in_lemma(MVar, Lemma):-
	theorem(_, Lemma, thm),
        matrix(_, LemmaMat, Lemma),
	meta_variable_occ_at(Lemma, _, MVar).


/******* OLD CODE *******/

wave_constr(WaveTerm, WaveConstr):-
    wave_fronts(Term, [WFPos-_|_], WaveTerm),
    exp_at(Term, WFPos, SubTerm),
    functor(SubTerm, WaveConstr, _).

waves_peter_out(Rn):-
    wave_rule(Rn, genw(_, RhsInsts), _),
    \+ (member(_-[_|_]-_-_, RhsInsts);
        member(_-_-_-[_|_], RhsInsts)).

coerce_wave_fronts(L, LL, SubstL):-
    match_wave_holes(L, LL),
    match_wave_fronts(L,LL,SubstL).

match_wave_holes(L, LL):-
    wave_fronts(_, [WFL-[WHL]/_], L),
    wave_fronts(_, [WFLL-[WHLL]/_], LL),
    append(WHL, WFL, PosL),
    append(WHLL, WFLL, PosLL),
    exp_at(L, PosL, WHole),
    exp_at(LL, PosLL, WHole).

match_waves(L, LL):-
    wave_fronts(EL, [PosL-WHPos], L),
    wave_fronts(ELL, [PosLL-WHPos], LL),
    exp_at(EL,  PosL,  Wave),
    exp_at(ELL, PosLL, Wave).

match_wave_fronts(L, LL):-
    wave_fronts(EL, [PosL-[WHPos]/_], L),
    wave_fronts(ELL, [PosLL-[WHPos]/_], LL),
    exp_at(EL,  PosL,  WaveL),
    exp_at(ELL, PosLL, WaveLL),
    replace(WHPos, _, WaveL, Front),
    replace(WHPos, _, WaveLL,Front).

match_wave_fronts(L, LL, SubstL):-
    partial_wave_front_at(L, Pos, Term1),
    exp_at(LL, Pos, Term2),
    match_terms(Term1, Term2, SubstL),
    apply_annsubst_list(SubstL, L, LL).

partial_wave_front_at(Term, Pos, SubTerm):-
    exp_at(Term, Pos, SubTerm),
    functor(SubTerm, Func, _),
    is_hov(Func),
    wave_fronts(UnAnnTerm, WFSpec, Term),
    member(WFPos-[WHPos]/[hard,_], WFSpec),
    append(SubPos, WFPos, Pos),
    \+ SubPos == WHPos.

match_terms(Term1, Term2, [[SkelTerm1, Arg]]):-
    Term1 =.. [F|Args],
    is_hov(F),
    member(Term2, Args),
    skeleton(Term1, SkelTerm1),
    SkelTerm1 =.. [_|SkelArgs],
    zip(ArgsSkelArgs, Args, SkelArgs),
    member(Term2-Arg, ArgsSkelArgs).

match_term_list([], []).
match_term_list([Term1-Term2|Terms], SubstList):-
    match_terms(Term1, Term2, Subst),
    match_term_list(Terms, SubstL),
    append(Subst, SubstL, SubstList).

    % Adjust wave-front spec to include trailing potehtial wave-fronts. 
    %
adjust_wave_front_spec([WFPos-[WHPos]/[hard,out]],SkelWHPos,NewWFSpec):-
    append(WHPos, WFPos, PWFPos),
    append([WFPos-[WHPos]/[hard,out]], [PWFPos-[SkelWHPos]/[_,out]], NewWFSpec).

annotate_subst_list([], _, []).
annotate_subst_list([Subst|SubstL], PWHPosWFSpec, [AnnSubst|AnnSubstL]):-
    annotate_subst(Subst, PWHPosWFSpec, AnnSubst),
    annotate_subst_list(SubstL, PWHPosWFSpec, AnnSubstL).
annotate_subst([Term1, Term2], [PWHPos,WFSpec], [AnnTerm1, AnnTerm2]):-
    maplist(WFSpec, WFPos-Rest:=>AdjWFPos-Rest, append(AdjWFPos, [_], WFPos), AdjWFSpec),
    wave_fronts(Term1, [[]-[PWHPos]/[_,out]], AnnTerm1),
    wave_fronts(Term2, AdjWFSpec, AnnTerm2).

skeletonize_subst_list([], []).
skeletonize_subst_list([Subst|SubstL], [SkelSubst|SkelSubstL]):-
    skeletonize_subst(Subst, SkelSubst),
    skeletonize_subst_list(SubstL, SkelSubstL).

skeletonize_subst([Term1, Term2], [SkelTerm1, SkelTerm2]):-
    wave_fronts(UnAnnTerm1, _, Term1),
    freevarsinterm(UnAnnTerm1, OVars),
    same_length(OVars, MVars),
    zip(OMVars, OVars, MVars),
    obj_to_meta_vars(OMVars, Term1, SkelTerm1),
    obj_to_meta_vars(OMVars, Term2, SkelTerm2).

apply_subst_list([], Term, Term).
apply_subst_list([Subst|SubstL], Term, NewTerm):-
    strip_meta_annotations(Subst, NSubst),
    apply_subst(NSubst, Term, NTerm),
    apply_subst_list(SubstL, NTerm, NewTerm).

apply_subst(Subst, Term, NewTerm):-
    copy(Subst, [T1, T2]),
    exp_at(Term, Pos, T1),!,
    replace(Pos, T2, Term, NTerm),
    apply_subst(Subst, NTerm, NewTerm).
apply_subst(_, Term, Term).

apply_annsubst_list([], Term, Term).
apply_annsubst_list([Subst|SubstL], Term, NewTerm):-
    apply_annsubst(Subst, Term, NTerm),
    apply_annsubst_list(SubstL, NTerm, NewTerm).

apply_annsubst(Subst, Term, NewTerm):-
    copy(Subst, [T1, T2]),
    exp_at(Term, Pos, T1),!,
    replace(Pos, T2, Term, NTerm),
    apply_annsubst(Subst, NTerm, NewTerm).
apply_annsubst(_, Term, Term).
    

obj_to_meta_vars([], Term, Term).
obj_to_meta_vars([OVar-MVar|OMVars], Term, NewTerm):-
    replace_all(OVar, MVar, Term, NTerm),
    obj_to_meta_vars(OMVars, NTerm, NewTerm).
    
meta_ripple_wave(WaveTerm, NewWaveTerm, NewSkeleton):-
    wave_fronts(Term, [_-[WH]/[hard,out]|InnerWaves], WaveTerm),
    wave_fronts(Term, [[]-[WH]/[hard,out]|InnerWaves], NewWaveTerm),
    exp_at(NewWaveTerm, WH, NewWaveHole),
    skeleton_term(NewWaveHole, NewSkeleton).

meta_ripple_wave(WaveTerm, NewWaveTerm, NewSkeleton):-
    wave_fronts(Term, [WF-[WH]/[hard,in]|InnerWaves], WaveTerm),
    append(WH, WF, NewWF),
    wave_fronts(Term, [NewWF-[WH]/[hard,in]|InnerWaves], NewWaveTerm),
    append(WH, NewWF, AbsNewWH),
    exp_at(NewWaveTerm, AbsNewWH, NewWaveHole),
    replace(NewWF, NewWaveHole, NewWaveTerm, NewSkeleton).

    % Selects single wave-terms with atomic
    % wave-functions.
single_wave_occ_at(Term, Pos, WaveTerm):-
    wave_occ_at(Term, Pos, WaveTerm),
    wave_fronts(_, WFSpec, WaveTerm),
    member([]-[WH]/[hard,in], WFSpec),
    exp_at(WaveTerm, WH, SubWaveTerm),
    \+ wave_fronts(_, [[]-_|_], SubWaveTerm).
single_wave_occ_at(Term, Pos, WaveTerm):-
    wave_occ_at(Term, Pos, WaveTerm),
    wave_fronts(_, [[_]-_/[hard,out]|_], WaveTerm).
    
adjust_wave_term_pos(Pos, Goal, AdjPos):-
    wave_fronts(_, WFSpec, Goal),
    member(WPos-[WH]/_, WFSpec),
    append(TPos, WPos, Pos),
    append(TPos1,[WH],TPos),
    append(TPos1,WPos,AdjPos).

ho_term_occ_in(G, Side):-
    matrix(_, M, G),
    ho_term_occ_in_(M, Side).
ho_term_occ_in_(Term = _ in _, left):-
    ho_term_in(Term).
ho_term_occ_in_(_ = Term in _, right):-
    ho_term_in(Term).
ho_term_in(Term):-
    exp_at(Term, _, SubTerm),
    \+ atomic(SubTerm),
    functor(SubTerm, Func, _),
    is_hov(Func).

definite_wave_occ_at(Exp, Pos, MSubExp):-
    \+ var(Exp),
    matrix(_,MExp,Exp),
    exp_at(MExp,Pos,MSubExp),
    \+ atomic(MSubExp),
    wave_fronts(_,WSpec,MSubExp),
    \+ WSpec = [], 
    \+ ([[_|_]-_/[_,in]|_] = WSpec),
    \+ (WSpec = [_-_/[Type,_]|_], var(Type)).
    %
    % \+ member([]-_/[_,out],WSpec).
    %
    % The last constraint rules-out out-bound waves which
    % have no associated wave-function. 

   
potential_wave_occ_at(Exp, Pos, MSubExp):-
    \+ var(Exp),
    matrix(_,MExp,Exp),
    exp_at(MExp,Pos,MSubExp),
    \+ atomic(MSubExp),
    wave_fronts(_,WSpec,MSubExp),
    \+ WSpec = [],
    %\+ (WSpec = [_-_/[Type,_]], \+ var(Type)),
    \+ (member(_-_/[Type,_], WSpec), \+ var(Type)),
    \+ member([]-_/[_,out], WSpec).
    
partial_wave_front(Exp):-
    wave_fronts(UnAnnExp, WFSpec, Exp),
    member(WFPos-[WHPos]/[hard,_], WFSpec),
    exp_at(UnAnnExp, WFPos, WaveTerm),
    exp_at(WaveTerm, Pos, SubTerm),
    \+ Pos == WHPos,
    is_hov(SubTerm).

erase_potential_waves(Matrix, NewMatrix, []):-
    \+ wave_fronts(_, [_|_], Matrix),
    sinks(NewMatrix, _, Matrix).
erase_potential_waves(Matrix, NewMatrix, [Subst|SubstL]):-
    wave_fronts(_, [WFPos-[WHPos]/[Soft,Dir]|_], Matrix),
    var(Soft),
    exp_at(Matrix, WFPos, WaveTerm),
    wave_fronts(UnAnnWaveTerm, _, WaveTerm),
    UnAnnWaveTerm =.. [Func|WaveTermArgs],
    same_length(WaveTermArgs, Args),
    hfree(Args, []),
    NWaveTerm =.. [Func|Args],
    wave_fronts(NWaveTerm, [[]-[WHPos]/[_,Dir]], AnnNWaveTerm),
    exp_at(NWaveTerm, WHPos, WHole),
    skeletonize_subst([AnnNWaveTerm, WHole], Subst),
    apply_annsubst_list([Subst], Matrix, NMatrix), 
    erase_potential_waves(NMatrix, NewMatrix, SubstL).


% generate_meta_variable/1
%
%
generate_meta_variable(MVar):-
	tag_with_number('M', hov_cnt, MVar).


% coerce_partial_lemma/2
%
%
coerce_partial_lemma(SubstL, NewSubstL):-
	coerce_annsubst_list(SubstL, SubstL1),
	lemma(SubstL, Name:Lemma1),
	apply_subst_list(SubstL1, Lemma1, Lemma2),
        eval_partial_lemma(Lemma2, SubstL2),
        apply_subst_list(SubstL2, Lemma2, NewLemma),
        \+ disprove([]==>NewLemma),
        append(SubstL1, SubstL2, NewSubstL).
coerce_partial_lemma(SubstL, SubstL).


/*
coerce_partial_lemma(SubstL, SubstL):-
	lemma(SubstL, Name:Lemma1),
        apply_subst_list(SubstL, Lemma1, Lemma2),
        recorded(theorem,theorem(_,_,_,Name),Ref),
        erase(Ref),
        findall(MetaTerm, meta_term_occ_at(Lemma2, _, MetaTerm), MetaTerms),
        add_dummy_defs(MetaTerms),
        add_thm(Name, []==>Lemma2),
        record_thm(Name, thm),
        add_wave_rules(Name, _).     % revise wave-rule schemas
*/


add_dummy_defs([]).
add_dummy_defs([H|T]):-
	add_def(H <==> void),
        add_dummy_defs(T).

% lemma/2 
%
% Used to locate lemma in which MTerm occurs. Require a more
% global/general recording mechanism for meta-variable usage.
%
lemma([[MTerm,_]|_], Name:Lemma):-
	wave_fronts(EMTerm, _, MTerm),
        copy(EMTerm, CEMTerm),
        theorem(Name, Lemma, thm),
	matrix(_, Mat, Lemma),
	meta_term_occ_at(Mat, _, CEMTerm).

coerce_annsubst_list([], []).
coerce_annsubst_list([Sub|SubL], [NSub|NSubL]):-
	coerce_annsubst(Sub, NSub),
	coerce_annsubst_list(SubL, NSubL).

coerce_annsubst([L, R], [L, NewR]):-
        wave_fronts(_, WFSpecL, R),
        findall(WF-WH/[Typ,Dir], (member(WF-WH/[Typ,Dir], WFSpecL), var(Typ)), PWFSpecL),
        replace_potential_waves(PWFSpecL, R, NewR).

replace_potential_waves([], Term, Term). 
replace_potential_waves([Pos-[WHPos]/_|Rest], Term, NewTerm):-
        append(WHPos, Pos, AbsWHPos),
        exp_at(Term, AbsWHPos, WHole),
	replace(Pos, WHole, Term, NTerm),
        replace_potential_waves(Rest, NTerm, NewTerm).

eval_partial_lemma(Lemma, SubstL):-
	matrix(Context, Mat, Lemma),
	eval_lemma(Context, Mat, SubstL),
        \+ SubstL = [].

eval_lemma(Context, Form, [Subst]):-
	member(Var:Typ, Context),
	build_term(Typ, Val),
	replace_all(Var, Val, Form, NForm),
	normalize(NForm, NewForm),
        extract_subst(NewForm, Subst).
eval_lemma(_, Form, [[SkelMTerm, SkelMArg]]):-
        meta_term_occ_at(Form, _, MTerm),
        skeleton(MTerm, SkelMTerm),
        SkelMTerm =.. [_|SkelMArgs],
        member(SkelMArg, SkelMArgs).
eval_lemma(Context, Form, []).

extract_subst(L = R in _, [SR,SL]):-
	is_meta_term(R),
        R =.. [MFunc|Args],
        same_length(Args, MArgs),
        zip(ArgsMArgs, Args, MArgs),
        % Filter-out constants
        filter_constants(ArgsMArgs, NArgsMArgs),
	obj_to_meta_vars(NArgsMArgs, L, SL),
        SR =.. [MFunc|MArgs].

filter_constants([], []).
filter_constants([Term-MVar|Rest], Result):-
	constant(Term, _),!,
        filter_constants(Rest, Result).
filter_constants([First|Rest], [First|Result]):-
	filter_constants(Rest, Result).




    


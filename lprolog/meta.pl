

/*******************************

 speculate_lemma/6

 *******************************/

speculate_lemma(H, G, BlkPos, WaveTerm, Name:([]==>Lemma), [SkelRHS,_]):-
    wave_fronts(Term, [WF-[WH]/[hard,out]], WaveTerm),
    append(WH,WF,AbsWH),
    exp_at(WaveTerm, AbsWH, WaveHole),
    hfree([WaveVar], H),
    wave_function_val_type(WaveTerm, WaveHoleTyp),
    convert_type(WaveVarTyp, WaveHoleTyp),
    append(H, [WaveVar:WaveVarTyp], NewH),
    replace(AbsWH, WaveVar, WaveTerm, AnnLHS),
    wave_skeleton(AnnLHS, WaveRuleSkel),
    wave_fronts(LHS, _, AnnLHS),
    vartypsinterm(LHS, NewH, VarTyps),
    zip(VarTyps, Vars, Types),
    super_term_type(G, BlkPos, HOV_val_typ),
    append([WaveHoleTyp|Types], [HOV_val_typ], HOV_typ_list),
    arity2list(HOV_typ, HOV_typ_list),
    generate_rhs_speculation([WaveRuleSkel|Vars], HOV_typ, RHS),
    skeleton(RHS, SkelRHS),
    convert_type(Type, HOV_val_typ),
    requantify(NewH, LHS = RHS in Type, Lemma),
    tag_with_number(lemma, lemma_cnt, Name),
    print_conjecture(Lemma, Name),
    format_plan_list([]).

speculate_sinks(H, G, BlockagePos, BlockageTerm, Rn, Dir, Name:([]==>Lemma)):-
    wave_skeleton(G, SkelG),
    wave_skeleton(BlockageTerm, SkelBlkTerm),
    nonblocked_side(SkelG, BlockagePos, SkelNonBlkTerm),
    wave_rule(Rn, genw(Dir, [_-[SinkPos-_]-_-[]]), _),
    SinkPos = [ArgPos|TermPos],
    super_term_type(BlockageTerm, TermPos, Arity),
    arity2list(Arity, LType),
    nth1(ArgPos, LType, LSinkType),
    generate_sink_spec(LSinkType, [], H, SinkVar, SinkSpec1),
    replace(SinkPos, SinkSpec1, SkelBlkTerm, NSkelBlkTerm),
    replace(BlockagePos, NSkelBlkTerm, SkelG, NSkelG),
    generate_sink_spec(LSinkType, [SkelNonBlkTerm], _, SinkVar, SinkSpec2),
    replace_all(SkelNonBlkTerm, SinkSpec2, NSkelG, NewSkelG),
    convert_type(SinkType, LSinkType),
    append(H, [SinkVar:SinkType], NewH),
    requantify(NewH, NewSkelG, Lemma),
    tag_with_number(lemma, lemma_cnt, Name).
    

nonblocked_side(_ = RHS in _, BlockagePos, RHS):-
    append(_, [1,1], BlockagePos).
nonblocked_side(LHS = _ in _, BlockagePos, LHS):-
    append(_, [2,1], BlockagePos).
    

generate_sink_spec(LSinkType, ArgL, H, Fov, SinkSpec):-
    maplist(ArgL, Arg:=>LTyp, (guess_type(Arg, Typ),
                               convert_type(Typ, LTyp)), ArgLTypL),
    append(ArgLTypL, [LSinkType, LSinkType], LTypL),
    arity2list(HovTyp, LTypL),
    generate_hov(HovTyp, Hov),
    generate_fov(SinkType, Fov, H),
    append(ArgL, [Fov], HovArgL),
    SinkSpec =.. [Hov|HovArgL],
    add_def(SinkSpec <==> void). % Required for Oyster parser :-(

generate_rhs_speculation(Args, Type, SpecWave):-
    generate_hov(Type, Var),
    SpecWave =.. [Var|Args],
    add_def(SpecWave <==> void). % Required in order to enable wave-rule parsing  :-(

super_term_type(Term, [], LTyp):-
    functor(Term, Func, _),
    type(clam, Func, LTyp).    
super_term_type(G, [_|Pos], LTyp):-
    matrix(_, M, G),
    exp_at(M, Pos, _ = _),!,
    append([_],NPos,Pos),
    exp_at(M,NPos,_ = _ in Typ),
    convert_type(Typ, LTyp).
super_term_type(G, [_|Pos], LTyp):-
    matrix(_, M, G),
    exp_at(M, Pos, Term),
    functor(Term, Func, _),
    type(clam, Func, LTyp).

vartypsinterm(Term, HypL, VarTyps):-
    freevarsinterm(Term, Vars),
    findall(Var-LTyp,(member(Var, Vars),
                      hyp(Var:Typ,HypL),
                      convert_type(Typ, LTyp)),VarTyps).

    % Equality type gives rise to a special case
    %
wave_skeleton(AnnEq in Typ, SkelEq in Typ):-
    wave_skeleton(AnnEq, SkelEq).

wave_skeleton(Wave, Skel):-
    Wave =.. [WaveFunc|WaveArgs],
    wave_skeleton_args(WaveArgs, SkelArgs),
    Skel =.. [WaveFunc|SkelArgs].

wave_skeleton_args([], []).
wave_skeleton_args([WaveArg|WaveArgs], [SkelArg|SkelArgs]):-
    wave_fronts(Term, [WF-[WH]/[hard,_]|_], WaveArg),!,
    append(WH, WF, AbsWH),
    exp_at(WaveArg, AbsWH, SubSkelArg),
    replace(WF, SubSkelArg, Term, SkelArg),
    wave_skeleton_args(WaveArgs, SkelArgs).
wave_skeleton_args([SkelArg|WaveArgs], [SkelArg|SkelArgs]):-
    wave_skeleton_args(WaveArgs, SkelArgs).

% Replaced by first-order version
%
% partial_wave_rule_match(Exp, Pos, Rn, MissingWaves):-
%     generate_hov_pattern(Exp, NewExp, HoVarPatts),
%     wave_fronts(Exp1, [Pos-_|_], NewExp),!,
%     wave_rule(Rn,genw(left, _),_=>LHS:=>_),   % Rule-out backward wave-rules :-(
%     wave_fronts(Exp2, _, LHS),
%     unify_ho_terms(Exp1, Exp2, _, NSubstL),
%     skeletonize_subst_list(NSubstL, SkelNSubstL),
%    missing_wave_skels(HoVarPatts, SkelNSubstL, MissingWaves),!.

partial_wave_rule_match(WaveTerm, WavePos, Rn, SkelWaveTerm):-
    wave_fronts(RawWaveTerm, [WavePos-[HolePos]/_|_], WaveTerm),
    length(WavePos, 1), % Note: currently restricted to simple
                        % wave-terms. Need to generalise to allow
                        % for composite wave-functions.
    skeleton(WaveTerm, SkelWaveTerm),
    wave_rule(Rn, _, _ => SkelWaveTerm :=> _),
    wave_fronts(RawSkelWaveTerm, [SkelWavePos-[SkelHolePos]/_|_], SkelWaveTerm),
    length(SkelWavePos, 1), % Note: currently restricted to simple
                            % wave-terms. Need to generalise to allow
                            % for composite wave-functions.
    append(SkelHolePos, SkelWavePos, AbsSkelHolePos),
    append(HolePos, WavePos, AbsHolePos),
    exp_at(WaveTerm, AbsHolePos, Hole),
    exp_at(SkelWaveTerm, AbsSkelHolePos, Hole),
    % Checking matching prefixes
    exp_at(RawWaveTerm, WavePos, RawWave),
    exp_at(RawSkelWaveTerm, SkelWavePos, RawSkelWave),
    RawWave =.. [WaveFunctor|_],
    RawSkelWave =.. [WaveFunctor|_].
    

    % skeleton_wave_term(WaveTerm, SkelWaveTerm, MWaves),
    % wave_rule(Rn, _, _ => SkelWaveTerm :=> _),
    % clean_wave_fronts(MWaves, MissingWaves),
    % refine_wave_term(WaveTerm, MissingWaves, NewWaveTerm).

refine_wave_term(WaveTerm, [], WaveTerm).
refine_wave_term(WaveTerm, [SkelWavePos-SkelWave|MWaves], NewWaveTerm):-
    wave_fronts(_, [_-[SkelHolePos]/_], SkelWave),
    exp_at(SkelWave, SkelHolePos, SkelHole),
    wave_fronts(_, WFSpec, WaveTerm),
    member(SkelWavePos-[HolePos]/_, WFSpec),
    append(HolePos, SkelWavePos, AbsSkelWavePos),
    exp_at(WaveTerm, AbsSkelWavePos, SkelHole),
    replace(SkelWavePos, SkelWave, WaveTerm, NWaveTerm),
    refine_wave_term(NWaveTerm, MWaves, NewWaveTerm).
    
skeleton_wave_term(Term, NTerm, MetaVars):-
    Term =.. [F|Args],
    % skeleton_wave_terms(Args, 1, NArgs, MetaVars),
    same_length(Args, MArgs),
    NTerm =.. [F|MArgs].

skeleton_wave_terms([], _, [], []).
skeleton_wave_terms([Term|Terms], Pos, [NTerm|NTerms], [MetaVar|MetaVars]):-
    skeleton_wave_term_(Term, [Pos], NTerm, MetaVar),
    NPos is Pos + 1,
    skeleton_wave_terms(Terms, NPos, NTerms, MetaVars).

skeleton_wave_term_(WTerm, Pos, SkelWTerm, AbsPos-MetaVar):-
    wave_fronts(Term, [[]-[WHPos]/TypDir], WTerm),!,
    wave_fronts(Term, [[]-[]/TypeDir], NWTerm),
    replace(WHPos, MetaVar, NWTerm, SkelWTerm),
    append(WHPos, Pos, AbsPos).
skeleton_wave_term_(Term, Pos, MetaVar, Pos-MetaVar).

clean_wave_fronts([], []).
clean_wave_fronts([_-'@wave_var@'(Term)|Terms], NTerms):- !,
    clean_wave_fronts(Terms, NTerms).
clean_wave_fronts([_-Var|Terms], NTerms):- 
    var(var),!,
    clean_wave_fronts(Terms, NTerms).
clean_wave_fronts([Pos-Term|Terms], [Pos-Term|NTerms]):-
    wave_fronts(_, [_|_], Term),!,
    clean_wave_fronts(Terms, NTerms).
clean_wave_fronts([Pos-Term|Terms], [Pos-'@wave_front@'(hard,out,Term)|NTerms]):-
    clean_wave_fronts(Terms, NTerms).

unify_ho_terms(T1, T2, NewT1, NNSubstL):-
    convert(T1, LT1),
    convert(T2, LT2),
    unify([[LT1,LT2]],_,SubstL),
    adjust_hov_names(SubstL, NSubstL),
    apply_subs_to_term(NSubstL, LT1, NewLT1),
    convert_to_p(NewT1, NewLT1),
    convert_substl(NSubstL, NNSubstL).

adjust_hov_names([], []).
adjust_hov_names([[cv(Var,Typ,Cat),Val]|SubstL],[[cv(Var,Typ,Cat),NVal]|NSubstL]):-
    is_hov(Var),
    replace_hovs(Val, NVal),
    adjust_hov_names(SubstL, NSubstL).
adjust_hov_names([Subst|SubstL], [Subst|NSubstL]):-
    adjust_hov_names(SubstL, NSubstL).

replace_hovs(cv(LVar, Type, v), cv(Var, Type, v)):-
    is_lp_hov(LVar),!,
    generate_hov(Type, Var).
replace_hovs(BVar\Body, BVar\NBody):-
    replace_hovs(Body, NBody).
replace_hovs(Term1^Term2, NTerm1^NTerm2):-
    replace_hovs(Term1, NTerm1),
    replace_hovs(Term2, NTerm2).
replace_hovs(cv(Const, Type, Cat), cv(Const, Type, Cat)).


    % Test for lambda prolog HO variable.
    %
is_lp_hov(Var):-
    name(Var, [86,97,114|_]).
    

weaken_wave_fronts([], []).
weaken_wave_fronts([H|T], [HH|TT]):-
    weaken_wave_front(H, HH),
    weaken_wave_fronts(T, TT).

weaken_wave_front(W, NW):-
    wave_fronts(W1, [WF-WHs/[Typ,Dir]], W),
    length(WHs, L),
    L > 1,!,
    select(_, WHs, NWHs),
    wave_fronts(W1, [WF-NWHs/[Typ,Dir]], NW).
weaken_wave_front(W, W).
    
missing_wave_skels([], _, []).
missing_wave_skels([Var-Patt|VarPatts], SubstL, [Skel|Skels]):-
    member([VarApp,_], SubstL),
    functor(VarApp, Var, _),
    wave_fronts(UnAnnPatt, WFSpec, Patt),
    apply_subst_list(SubstL, UnAnnPatt, NewUnAnnPatt),
    wave_fronts(NewUnAnnPatt, WFSpec, NewPatt),
    weaken_wave_front(NewPatt, WNewPatt), 
    generate_wave_skel(WNewPatt, Skel),
    missing_wave_skels(VarPatts, SubstL, Skels).
missing_wave_skels([_|VarPatts], SubstL, Skels):-
    missing_wave_skels(VarPatts, SubstL, Skels).
    
generate_wave_skel(Var, _):-
    var(Var),!.
generate_wave_skel(Atom, _):-
    atom(Atom),!.
generate_wave_skel('@sink@'(T), T):-!.
generate_wave_skel('@wave_var@'(_), '@wave_var@'(_)):-!.
generate_wave_skel('@wave_front@'(Typ,Dir,Term), '@wave_front@'(Typ,Dir,NTerm)):-
    Term =..[F|Arg],
    is_hov(F),!,
    generate_wave_skel_list(Arg, [NTerm]).
generate_wave_skel('@wave_front@'(Typ,Dir,Term), '@wave_front@'(Typ,Dir,NTerm)):-
    Term =..[F|Args],!,
    generate_wave_skel_list(Args, NArgs),
    NTerm =.. [F|NArgs].
generate_wave_skel(Term, NTerm):-
    Term =..[F|Arg],
    is_hov(F),!,
    generate_wave_skel_list(Arg, [NTerm]).
generate_wave_skel(Term, NTerm):-
    Term =..[F|Args],!,
    generate_wave_skel_list(Args, NArgs),
    NTerm =.. [F|NArgs].

generate_wave_skel_list([], []).
generate_wave_skel_list([Term|Terms], [NTerm|NTerms]):-
    generate_wave_skel(Term, NTerm),
    generate_wave_skel_list(Terms, NTerms).

generate_hov_pattern(Exp, NewExp, HoVarPatts):-
    sinks(Exp0, _, Exp),
    elim_nested_waves(Exp0, Exp1),
    wave_function(Exp1, Func),
    arg_types(Func, TypArgs),
    skel_args(Args, PosArgs, Func, Exp1),
    generate_potential_waves(Args, TypArgs, HoVars, PWs),
    zip(PWsPosArgs, PWs, PosArgs),
    zip(HoVarPatts, HoVars, PWs),
    replace_list(PWsPosArgs, Exp1, NewExp),!.

elim_nested_waves(Exp, NewExp):-
    wave_fronts(RawExp, [WFSpec|_], Exp),
    wave_fronts(RawExp, [WFSpec], NewExp).

replace_list([],E,E).
replace_list([SubE-SubPos|T],Exp,NewExp):- 
    replace(SubPos,SubE,Exp,IntExp),
    replace_list(T,IntExp,NewExp).

generate_potential_waves([], [], [], []).
generate_potential_waves([Arg|Args], [Typ|Typs], [Var|Vars], [PWave|PWaves]):-
    generate_hov(Typ--->Typ, Var),
    Term =.. [Var,Arg],
    wave_fronts(Term, [[]-[[1]]/[hard,out]], PWave),
    generate_potential_waves(Args, Typs, Vars, PWaves).
    
generate_hov(Typ, Var):-
    gen_hov(Var),
    asserta(type(clam, Var, Typ)),
    add_env(Var-[Var-v]).

gen_hov(Var):-
    tag_with_number(hov, hov_cnt, Var).

generate_fov(Typ, Var, H):-
    var(Var),
    gen_fov(Var, H),
    asserta(type(clam, Var, Typ)),
    add_env(Var-[Var-c]).
generate_fov(_, Var, _):-
    is_fov(Var).

gen_fov(Var, H):-
    hfree([Var], H).

is_hov(Var):-
    atom(Var),
    name(Var, [104,111,118|_]).

is_fov(Var):-
    atom(Var),
    name(Var, [118|_]).

skel_args(Args, PosArgs, Func, Exp):-
    Exp =.. [Func|Terms],
    skel_args_(Terms, 1, Args, PosArgs).

skel_args_([], _, [], []).
skel_args_([H|T], Pos, [H|T1], [[Pos]|T2]):-
    \+ wave_fronts(_, [_|_], H),
    NPos is Pos + 1,
    skel_args_(T, NPos, T1, T2).
skel_args_([H|T], Pos, [SubH|T1], [AbsPos|T2]):-
    wave_holes([SubH], [RelPos], H),
    append(RelPos, [Pos], AbsPos),
    NPos is Pos + 1,
    skel_args_(T, NPos, T1, T2).

wave_holes(WHs, AbsWHs, Exp):-
    wave_fronts(_, WFSpec, Exp),
    wave_holes_(WFSpec, Exp, WHs, AbsWHs).

wave_holes_([], _, [], []).
wave_holes_([WFPos-RelWHs/_|WFSpec], Exp, WHsAll, AbsWHsALL):-
    maplist(RelWHs, RelPos:=>AbsPos, append(RelPos, WFPos, AbsPos), AbsWHs),
    findset(WH, (member(WHPos, AbsWHs), exp_at(Exp, WHPos, WH)), WHs),
    wave_holes_(WFSpec, Exp, WHsRest, AbsWHsRest),
    append(WHs, WHsRest, WHsAll),
    append(AbsWHs, AbsWHsRest, AbsWHsALL).

arity2list(Typ1 ---> Typ, [Typ1|Typ2]):-
    arity2list(Typ, Typ2).
arity2list(Typ, [Typ]).

arg_types(Func, Types):-
    type(clam, Func, FuncTyp),
    arity2list(FuncTyp, TypList),
    reverse(TypList,[_|TL]),
    reverse(TL, Types).
    
wave_function(WaveTerm, WaveFunc):-
    wave_fronts(_, [[_|WF]-WHs/[_,out]|_], WaveTerm),
    exp_at(WaveTerm, WF, WaveOcc),
    WaveOcc =.. [WaveFunc|_].
wave_function(WaveTerm, WaveFunc):-
    wave_fronts(_, [WF-[WH]/[_,in]|_], WaveTerm),
    append(WH, WF, AbsWH),
    exp_at(WaveTerm, AbsWH, HoleOcc),
    HoleOcc =.. [WaveFunc|_].

wave_function_type(WaveTerm, WaveFuncTyp):-
    wave_function(WaveTerm, WaveFunc),
    type(clam, WaveFunc, WaveFuncTyp).

wave_function_val_type(WaveTerm, WaveFuncValTyp):-
    wave_function_type(WaveTerm, WaveFuncTyp),
    val_type(WaveFuncTyp, WaveFuncValTyp).

val_type(_ ---> Typ, TTyp):-
    val_type(Typ, TTyp).
val_type(Typ, Typ).

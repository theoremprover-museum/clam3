%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% img/mrg/29-sept-92
% code to convert from prolog term to LP-term
% Env is an environment (name,realname) list
% as in Lambdaprolog

:- dynamic hov_to_lam_var/2.

% convert(PTerm,LTerm)
  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

init_env(Name):-
    delete_env(Name).

print_env(Name):-
    recorded(Name, environment(Env), _),
    write('=========================='),nl,
    writef('Environment for %t:\n\n',[Name]),
    print_env_list(Env),
    write('=========================='),nl.

print_env_list([]).
print_env_list([Var-[_-c]|Env]):-
    type(clam, Var, Type),
    writef('%t : %t (constant)\n',[Var, Type]),
    print_env_list(Env).
print_env_list([Var-[_-v]|Env]):-
    type(clam, Var, Type),
    writef('%t : %t (variable)\n',[Var, Type]),
    print_env_list(Env).

delete_env:-
    current_goaltree(Name),
    delete_env(Name).

delete_env(Name):-
    recorded(Name, environment(Env), _),
    delete_vartypes(Env),
    uniq_recorda(Name, environment([]), _).
delete_env(Name):-
    uniq_recorda(Name, environment([]), _).


update_env(H==>G):-
    current_goaltree(Name),
    update_env(Name, H==>G).

update_env(Name, Sequent):-
    extract_obj_bindings(Sequent, Bindings),
    update_env_(Name, Bindings).
    
update_env_(Name, VarTyps):-
    recorded(Name, environment(Env), _),!,
    delete_all_fov(Env, CleanEnv),
    update_env(VarTyps, CleanEnv, NewEnv),
    uniq_recorda(Name, environment(NewEnv), _). 
update_env_(Name, VarTyps):-
    update_env(VarTyps, [], NewEnv),
    uniq_recorda(Name, environment(NewEnv), _).

update_env([], NewEnv, NewEnv).
update_env([(Var:_)-c|VarTyps], EnvSofar, NewEnv):-
    member(Var-_, EnvSofar),!,
    update_env(VarTyps, EnvSofar, NewEnv).
update_env([(Var:Typ)-c|VarTyps], EnvSofar, NewEnv):-
    convert_type(Typ, LTyp),
    asserta(type(clam, Var, LTyp)),
    union([EnvSofar,[Var-[Var-c]]], NEnvSofar), 
    update_env(VarTyps, NEnvSofar, NewEnv).
update_env([(Var:Typ)-v|VarTyps], EnvSofar, NewEnv):-
    asserta(type(clam, Var, Typ)),
    union([EnvSofar,[Var-[Var-v]]], NEnvSofar),
    update_env(VarTyps, NEnvSofar, NewEnv).
    
delete_all_fov([], []).
delete_all_fov([Var-_|Bindings], NBindings):-
    is_fov(Var),!,
    delete_all_fov(Bindings, NBindings).
delete_all_fov([Bind|Bindings], [Bind|NBindings]):-
    delete_all_fov(Bindings, NBindings).

delete_vartypes([]).
delete_vartypes([V-_|T]):-
    retract(type(clam, V, _)),
    delete_hov_oyster_def(V),
    delete_vartypes(T).

delete_hov_oyster_def(V):-
    is_hov(V),
    erase_def(V).
delete_hov_oyster_def(_).

add_env(Binding):-
    current_goaltree(Name),
    add_env(Name, Binding).

add_env(Name, Binding):- 
    recorded(Name, environment(Env), _),!,
    union([Env,[Binding]],NewEnv),
    uniq_recorda(Name, environment(NewEnv), _).
add_env(Name, Binding):-
    uniq_recorda(Name, environment([Binding]), _).

convert_type(T list, list^T):- !.
convert_type(T, T).

extract_obj_bindings(H==>G, Bindings):-
    matrix(VarTyps1, _, G),
    findall(Var:Typ,hyp(Var:Typ,H),VarTyps2),
    append(VarTyps1, VarTyps2, VarTyps), 
    maplist(VarTyps, I:=>O, O = I-c, Bindings).

convert(Atom,cv(Name,Type,VarOrConst)) :-
    atomic(Atom), \+ var(Atom),!,
    lookup(Atom,Name-Type-VarOrConst).
    
convert(Atom,cv(Atom,_,v)) :-
    var(Atom),!,
    gensym(v,Atom),			% need to assert into env.
    add_env(Atom-[Atom-v]),
    assertz(type(clam,Atom,_)).    

convert(H::T,LPTerm) :- % infix is a nuisance
    !,Head = :: ,
    Rest = [H,T],
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
       make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).
convert(L & R,LPTerm) :- % infix is a nuisance
    !,Head = pair ,
    Rest = [L,R],
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
       make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).
convert(L => R,LPTerm) :- % infix is a nuisance
    !,Head = fsc ,
    Rest = [L,R],
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
       make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).

convert(L # R,LPTerm) :- % infix is a nuisance
    !,Head = hash ,
    Rest = [L,R],
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
       make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).
convert(L = R,LPTerm) :- % infix is a nuisance
    !,Head = equal ,
    Rest = [L,R],
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
       make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).

convert(Term,LPTerm) :-
    \+ atomic(Term),!,
    Term =.. [Head|Rest] ,
    convert_map(Rest,LPRest),
    convert(Head,NewHead),
    make_compose(NewHead,LPRest,LPT),
    (length(Rest,1) -> (LPTerm = LPT);
                       (LPTerm = (LPT))).
 
convert_map([],[]).
convert_map([T1|Rest],[LPT1|RestLP]) :-
    convert(T1,LPT1),
    convert_map(Rest,RestLP).

make_compose(T,[],T).
make_compose(T,[T1|Rest],Comp) :- make_compose(T^T1,Rest,Comp).

make_appl([],_) :- write('domain error, make_appl'),nl,!,fail.
make_appl([T],T) :- !.
make_appl([T|Rest],T ^ Restapp) :-
    make_appl(Rest,Restapp),!.

    % convert_substl/2 converts a lambda-prolog substitution
    % into prolog eliminating irrelevant substitutions
convert_substl([], []).
convert_substl([[cv(Var, Typ, _), LamTerm]|LPSubstL], [[FO_PatL, FO_PatR]|PSubstL]):-
    is_hov(Var),!,
    arity(Typ, Arity),
    functor(FO_PatL, Var, Arity),
    FO_PatL =..[_|Args],
    hfree(Args,[]),
    convert_lambda_term(Args, LamTerm, FO_PatR),
    convert_substl(LPSubstL, PSubstL).
convert_substl([_|LPSubstL], PSubstL):-
    convert_substl(LPSubstL, PSubstL).

convert_lambda_term(MVars, Term, NTerm):-
    conv_lambda_term(MVars, [], Term, NTerm).
conv_lambda_term([MVar|MVars], MVarSofar, cv(BVar,_,_)\Term, NTerm):-
    conv_lambda_term(MVars, [MVar-BVar|MVarSofar], Term, NTerm).
conv_lambda_term([], MVarSofar, Term, NTerm):-
    conv_lambda_term_(MVarSofar, Term, NTerm).

conv_lambda_term_(MBVars, cv(BVar,_,_), MVar):-
    member(MVar-BVar, MBVars),!.
conv_lambda_term_(_, cv(Arg,_,_), Arg).
conv_lambda_term_(MBVars, LPTerm, PTerm):-
    conv_lambda_term_map(MBVars, TList, LPTerm),
    PTerm =.. TList.

conv_lambda_term_map(MBVars, TList, T^A):-
    conv_lambda_term_map(MBVars, Rest, T),
    conv_lambda_term_(MBVars, A, V),
    append(Rest, [V], TList).
conv_lambda_term_map(MBVars, [U], T):-
    \+ T = _^_,
    conv_lambda_term_(MBVars, T, U).

arity(Typ, Arity):-
    arity(Typ, 0, Arity).
arity(T1 ---> T2, N, Arity):-
    M is N + 1,!,
    arity(T2, M, Arity).
arity(_, Arity, Arity).


lookup(K,S):- 
    current_goaltree(Name),
    recorded(Name, environment(Env), _), 
    lookup_(K,Env,S),!.

lookup_(Key,[],Key-Type-c):- 
    type(clam,Key,Type).
lookup_(NKey,[],Key-Type-v):-
    hov_to_lam_var(NKey, Key).
%%% Redundant since conversion is now 
%%% performed immediately after unification
%%% (within unify_ho_terms/4).
%%% lookup_(NKey,[],Key-Type-v):-
%%%    generate_hov(Type, NKey),
%%%    asserta(hov_to_lam_var(NKey, Key)).
lookup_(Key,[Key-[RealName-CV]|Env],RealName-Type-CV) :-
    type(clam,RealName,Type).
lookup_(Key,[OtherKey-_|Env],Value) :-
    lookup_(Key,Env,Value).

%%%%%%%%%%%%%%%%

fix_infix(A,A) :- atom(A),!.
fix_infix(::(A,B),AA::BB) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(pair(A,B),(AA & BB)) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(fsc(A,B),(AA => BB)) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(colon(A,B),(AA : BB)) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(hash(A,B),(AA # BB)) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(equal(A,B),(AA = BB)) :- !,fix_infix(A,AA), fix_infix(B,BB).
fix_infix(T,TT)  :-
    T =.. [Head|Body], 
    \+ is_hov(Head),!,
    fix_infix_map(Body,BodyFix), 
    TT =.. [Head|BodyFix].
fix_infix(T,T).

fix_infix_map([],[]).
fix_infix_map([T|Ts],[Tf|Tfs]) :-
    fix_infix(T,Tf),
    fix_infix_map(Ts,Tfs).

convert_to_p(T,Tlp) :-
    conv_back(TT,Tlp),!,
    fix_infix(TT,T).

conv_back(Atom,cv(Name,Type,VarOrConst)) :-
    var(Atom),
    lookup(Atom,Name-Type-VarOrConst).
conv_back(Atom,cv(Atom,_,v)).

conv_back(Term,LPTerm) :-
    conv_map(List,LPTerm),
    Term =.. List.
 


conv_map(Term_list,T^A) :-
    conv_map(Rest,T),
    conv_back(V,A),
    append(Rest,[V],Term_list).

conv_map([U],T) :-
    \+ T = _^_,
    conv_back(U,T).
   

apply_subs_to_sequent(Subs,H==>G,NewH==>NewG) :-
    matrix_c(A,E,Gmat,G),
    convert(Gmat,GmatLP),
    apply_subs_to_term(Subs,GmatLP,GmatLPSub),
    convert_to_p(NewGmat,GmatLPSub),
    matrix_c(A,E,NewGmat,NewG),
    convert_prop_list(Subs,H,NewH).
  
apply_subs_to_sequent_list(Subs,[],[]).
apply_subs_to_sequent_list(Subs,[S|Ss],[SS|SSs]) :-
    apply_subs_to_sequent(Subs,S,SS),
    apply_subs_to_sequent_list(Subs,Ss,SSs).


convert_prop_list(Subs,[],[]).
convert_prop_list(Subs,[ih:[R,H]|Hs],[ih:[R,NewH]|NewHs]) :-
    matrix_c(A,E,Hmat,H),
    convert(Hmat,HmatLP),
    apply_subs_to_term(Subs,HmatLP,HmatLPSub),
    convert_to_p(HmatSub,HmatLPSub),
    matrix_c(A,E,HmatSub,NewH),
    convert_prop_list(Subs,Hs,NewHs).
convert_prop_list(Subs,[H|Hs],[NewH|NewHs]) :-
    matrix_c(A,E,Hmat,H),
    convert(Hmat,HmatLP),
    apply_subs_to_term(Subs,HmatLP,HmatLPSub),
    convert_to_p(HmatSub,HmatLPSub),
    matrix_c(A,E,HmatSub,NewH),
    convert_prop_list(Subs,Hs,NewHs).

/*
 * same as matrix/4, but does not perform substitution of
 * existentials
 */
matrix_c([],[],T1,T1) :- T1 \= (_:_=>_), T1 \= (_:_#_).
matrix_c([V:T|As],Es,T1,V:T=>T2) :- matrix_c(As,Es,T1,T2).
matrix_c(As,[V-V:T|Es],T1,V:T#T2) :- 
			\+ var(T1),
			matrix_c(As,Es,T1,T2).
matrix_c(As,[MetaV-VV:T|Es],T1,V:T#T2) :- 
                        var(T1),
		        wave_fronts(VV,_,V),
			matrix_c(As,Es,T1,T2).






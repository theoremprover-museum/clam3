
/* Beginnings of a lib_create */
lib_create(trs(default)) :-
    if(lib_present(trs(default)),lib_delete(trs(default))),
    uniq_recorda(registry,registry(positive,[in/ms],_),_),
    uniq_recorda(registry,registry(negative,[in/ms],_),_).

lib_create(defeqn(Name)):-
    read_type(Name, Type),
    write('Enter equations for... ("eod." to finish)'),nl,
    read_equations(Name, Type, 1),
    writef('Use lib_save(defeqn(%t)) to save and parse your definition.',[Name]),nl.

read_type(Name, Dm => Rn):-
        writef('Enter type for %t: ',[Name]),
        readfile(user, Dm => Rn),
        generate_args(Dm, Args),
        concat_atom([Name], NameSynth),
        NameArgs =.. [Name|Args],
        TermOfSynth =.. [term_of, NameSynth],
        generate_appl(TermOfSynth, Args, Defn),
        generate_synth_thm(Dm, Args, Rn, ThmSynth),
        add_thm(NameSynth, ThmSynth),
        record_thm(NameSynth, synth),
        add_def(NameArgs <==> Defn).

        % generate_synth_thm/4
        %
        %
generate_synth_thm(Dm, Args, Rn, []==>ThmSynth):-
        gen_synth_thm(Dm, Args, Rn, ThmSynth).

gen_synth_thm(Typ # Typs, [Arg|Args], RnTyp, Arg:Typ => Body):-
	gen_synth_thm(Typs, Args, RnTyp, Body).
gen_synth_thm(Typ, [Arg], RnTyp, Arg:Typ => RnTyp):-
        member(Typ, [int, list(int), pnat, list(pnat)]).
	
        % generate_args/2
        %
        %
generate_args(Type, Args):-
	generate_args_(Type, Args),
        make_ground(Args).
generate_args_(_ # Typs, [_|Args]):-
        generate_args_(Typs, Args).
generate_args_(_, [_]).

        % generate_appl/3
        %
        %
generate_appl(Func, [], Func).
generate_appl(Func, [Arg|Args], FuncApp):-
	generate_appl(Func of Arg, Args, FuncApp).

        % read_equations/3
        %
        %
read_equations(Eqn, Type, Cnt):-
    concat_atom([Eqn, Cnt], EqnCnt),
    writef('%t: ', [EqnCnt]),
    read_equation(EqnCnt, Type, Equation),
    (Equation = eod 
      -> writef("Defintion of %t completed.\n",[Eqn])
      ;  (NCnt is Cnt + 1,
	  read_equations(Eqn, Type, NCnt))).
read_equations(_Eqn, _Type, _Cnt):-
    nl,write('Bad defintion (syntax?)'), nl.



        % read_equation/2
        %
        %
read_equation(EqnCnt, DmType => RnType, Equation):-
    readfile(user, Equation),
    (\+ Equation = eod 
      -> ((Equation = (LHS = RHS)
	    -> Cond = []	%empty Condition
	    ;  Equation = (Cond => (LHS = RHS))),
	  generate_bindings(DmType, Cond => (LHS = RHS), Bindings),
	  (Cond = []
	    -> matrix(Bindings, LHS = RHS in RnType, EqnThm)
	    ;  matrix(Bindings, Cond => (LHS = RHS in RnType), EqnThm)),
	  add_thm(EqnCnt, []==>EqnThm),
	  record_thm(EqnCnt, eqn))
      ;  true).

        % generate_bindings/3
        %
        %
generate_bindings(Type, [] => LHS = RHS, Bindings):-
    freevarsinterm(LHS, VarsLHS),
    freevarsinterm(RHS, VarsRHS),
    subset(VarsRHS, VarsLHS),
    gen_bindings(Type, LHS, VarsLHS, Bindings).
generate_bindings(Type, Cond => LHS = RHS, Bindings):-
    \+Cond = [],
    freevarsinterm(LHS, VarsLHS),
    freevarsinterm(RHS, VarsRHS),
    freevarsinterm(Cond, VarsCond),
    (subset(VarsCond, VarsLHS)
      -> (subset(VarsRHS, VarsLHS) 
          -> gen_bindings(Type, LHS, VarsLHS, Bindings)
          ;  writef("Freevariables of rhs %t are not subset of those in lhs %t\n",[RHS,LHS]))
      ; writef("Freevariables of condition %t are not subset of those in lhs %t\n",[Cond,LHS])).

        % gen_bindings/3
        %
        %
gen_bindings(Type, Term, Vars, VarTyps):-
	Term =.. [_|Args],
        type_terms(Type, Args, ArgsTyps),
        type_vars(ArgsTyps, Vars, VarTyps).

type_terms(Typ # Type, [Arg|Args], [Arg-Typ|ArgsTyps]):- !,
	type_terms(Type, Args, ArgsTyps).
type_terms(Typ, [Arg], [Arg-Typ]).

type_vars([], _, []).
        %
        % varibale case
        %
type_vars([Term-Typ|TermTyps], Vars, [Term:Typ|Bindings]):-
	member(Term, Vars),
	type_vars(TermTyps, Vars, Bindings).
        %
        % constant case
        %
type_vars([Term-Typ|TermTyps], Vars, Bindings):-
	oyster_type(Typ, _, [Term]),  
        type_vars(TermTyps, Vars, Bindings).
	% 
        % constructor case
        %
type_vars([Term-Typ|TermTyps], Vars, Bindings):-
        oyster_type(Typ, [Term], _),
        decomp_term_typs(Term, Typ, TTs),
        append(TTs, TermTyps, NewTermTyps),
        type_vars(NewTermTyps, Vars, Bindings).

decomp_term_typs(s(X), pnat, [X-pnat]).
decomp_term_typs(X::Y, Z list, [X-Z, Y-(Z list)]).



  






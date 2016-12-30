/* 
 * CLAM.v3.2
 *
 * Conjecture disprover code.
 * 
 */


% disprove/1
%
%
disprove(_==>AnnG):-
    strip_meta_annotations(AnnG, G),
    matrix(_, Mat, G),
    contains_meta_variables(Mat),!,fail.
disprove(H==>AnnG):-
    strip_meta_annotations(AnnG, G),
    matrix(Vars, Mat, G),
    append(H, Vars, Binds),
    disprove(Binds, Mat).

disprove(Binds, Form):-
    freevarsinterm(Form, Vars),
    ground_vars(Binds, Vars, Form, NewForm),
    normalize(NewForm, NormNewForm),
    \+ elementary([]==>NormNewForm, _),
    writef("\n   Counter example: %t\n", [NormNewForm]).

normalize(Term, NewTerm):-
	exp_at(Term, Pos, STerm),
        func_defeqn(_, _:Cond=>STerm :=> NSTerm),
        (elementary([]==>Cond, _);
         (Cond = [CT],
          normalize(CT, {true}))),!,
        replace(Pos, NSTerm, Term, NTerm),
        normalize(NTerm, NewTerm),!.
normalize(Term, NewTerm):-
	cancel(Term, NewTerm).
normalize(Term, Term).

disprove_(0 = s(_) in pnat).
disprove_(s(_) = 0 in pnat).
disprove_(nil = _::_ in _ list).
disprove_(_::_ = nil in _ list).

ground_vars(_, [], Form, Form).
ground_vars(Binds, [Var|Vars], Form, NewForm):-
    hyp(Var:Typ, Binds),
    build_term(Typ, Val),
    replace_all(Var, Val, Form, NForm),
    ground_vars(Binds, Vars, NForm, NewForm).

build_term(Typ, Val):-
	build_ground_term(Typ, Val),
        termsize(Val, N), (((N > 4),!,fail);(true)).

build_ground_term(pnat, Val):-
	member(Val, [0,s(0)]).
build_ground_term(Typ list, nil).
build_ground_term(Typ list, X::Y::nil):-
        build_ground_term(Typ, X),
        build_ground_term(Typ, Y).

termsize(X, 1):-
	atomic(X).
termsize(X, N):-
        \+ atomic(X),
	X =.. [F|Args],
        length(Args, M),
        N is M+1,!.
        

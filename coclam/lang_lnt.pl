/******************************************************************************
File: lang.pl
Author: Louise Dennis

For use with Coinduction in Clam.  Predicates that relate to specific datatypes
*******************************************************************************/

/* 1st September tran_type added.  ? how does find_NewG label infinite trees ? */

%% find_NewG(+Type, +Destructor, +Vs, +Term, -Goal)
%% Constructs a new goal of an appropriate type, depending on Type and
%% Destructor.
find_NewG(C list, hd, Vs, Sinks, NewG, Conds):-
	matrix_conds(Vs, Conds, Sinks, C, NewG).
find_NewG(bintree(C), label, Vs, Sinks, NewG, Conds):-
	matrix_conds(Vs, Conds, Sinks, C, NewG).
find_NewG(Type, Tran, Vs, Term, NewG, Conds):-
	\+ (Type = _ list, Tran =hd),
	\+ (Type = bintree(_), Tran = label),
	\+ (Type = tree(_), Tran = label),
	matrix_conds(Vs, Conds, Term, Type, NewG).

tran_type(C list, hd, C):-!.
tran_type(bintree(C), label, C):-!.
tran_type(tree(C), label, C):-!.
tran_type(tree(C), tree, list(tree(C))):-!.
tran_type(T, _, T).
%% inv(?Constructor, ?Destructor, ?Argument, ?Term)
%% Relates Constructors and Destructors.
inv(Con, Pred, ArgNum, _):-transition(_, Term, Pred, Result),
	                   Term =.. [Con|Args],
			   nth(ArgNum, Args, Result).
			   
%% Last Clause for use with generalisation critic - may need some work.
inv(of, Inv, P, [H|T]):-
	\+ var(H),
	inv(H, Inv, P, T),
	\+ H == of.
	
inv(Con, Pred, ArgNum):-inv(Con, Pred, ArgNum,_).

%% ofE(+Term, -Destructor, -Subterm)
%% For use with generalisation critic - trying to find destructor and subterm 
%% within ofs.
ofE(E1, Inv, E2):-
	E1 =.. [of|[Inv|E2]].
ofE(E1, Inv, E2):-
	E1 =.. [of|List],
	List = [H|_],
	atomic(H),
	E3 =.. List,
	ofE(E3, Inv, E2).
	
%% base_type(+Type, -Bot)
%% Relates type with their Bottom element
%% ?? Can base and con_type be combined ?
base_type(Type, Base, Dep):- data(Base, Type, Dep, non_rec),
	                \+ member(V:Type, Dep),
			\+ member(V:list(Type), Dep).
base_type(Type, Base):-base_type(Type, Base, _).

%% con_type(+Type, +Constuctor, +Arguments)
%% Relates a Type with its constructor and the number of arguments that 
%% constructor takes.

con_type(Type, Con, Args):-data(Term, Type, Dep, rec),
	(member(V:Type, Dep); member(V:list(Type), Dep)),
	Term =.. [Con|Arg],
	length(Arg, Args).

con_type(Type, Term, Args, Dep):- data(Term, Type, Dep, rec),
		(member(V:Type, Dep); member(V:list(Type), Dep)),
		Term =.. [Con|Arg],
		length(Arg, Args).

%% type_info(+Type, ?Constuctor, ?Base, ?Arguments)
type_info(Type, Con, Base, Args):- base_type(Type, Base),
	                           con_type(Type, Con, Args).


%% typ(+Type, +Argument, -Type)
%% Gives the type of an argument to a constructor of first Type ? Can argument 
%% be changed from a list.
typ(Type, [ArgNum], ArgType):-data(Term, Type, Dep, _),
	\+ atomic(Term), \+ var(Term),
	Term =.. [Con|Args],
	nth(ArgNum, Args, N),
	member(N:ArgType, Dep).

%% dont(+RuleName)
%% Stopping unwanted evaluation taking place.  I'm working on a better way to 
%% encode this in the eval_def method.
dont(iterates1).
dont(lswap1).
dont(lconst1).
dont(infinity1).
dont(h1).
dont(jump1).
dont(lswap21).
dont(infl11).
dont(tconst1).
dont(tconsti1).
dont(tswap1).
dont(tswap21).
dont(tswap31).
dont(from1).
dont(lminus2).
dont(loop1).
dont(tock1).
dont(tick1).

appn(apn2).
appn(sapn2).
appn(ssapn2).
appn(conapn2).
appn(timesapn2).
appn(plusapn2).

%% sort_type(+Term_Types, -Vars_Type)
%% Takes a list of terms with their types and returns a list of variables with 
%% their types.
sort_type([], []):-!.
sort_type([Term:Type|T], Out):-
	\+ var(Term), \+ atomic(Term),
	data(Term, Type, Deps, _),
	append(Deps, T, List),
	sort_type(List, Out).
sort_type([Term:Type|T], [Term:Type|Out]):-
	var(Term),
	sort_type(T, Out).
sort_type([Term:Type|T], Out):-
	atomic(Term),
	sort_type(T, Out).

type_of(V, Term, O, Vs, _, Type):-
	exp_at(O, Pos, V),
	exp_at(Term, Pos, V1),
	member(V1:Type, Vs), !.
type_of(V, Term, O, Vs, _, Type):-
	(exp_at(O, Pos, s(V)); exp_at(O, Pos, _::V)),
	exp_at(Term, Pos, V1),
	member(V1:Type, Vs), !.
type_of(V, Term, O, Vs, _, Type):-
	exp_at(O, Pos, V::_),
	exp_at(Term, Pos, V1),
	member(V1:Type list, Vs), !.
type_of(V, Term, O, Vs, Scheme, Ty):-
	difference_set(Vs, [Scheme], Set),
	exp_at(Term, Pos, V1),
	member(V1, Set),
	exp_at(O, Pos, VA),
	\+ atomic(VA),
	exp_at(O, PosT, V),
	end_segment(Pos, PosT, Left),
	member(V1:Type, Vs),
	typ(Type, Left, Ty), !.

function_d(_, nil-_ list:[]=>nil:=>nil).
function_d(_, nil-pnat:[]=>0:=>0).
function_d(_, nil-_ tree:[]=>leaf(A):=>leaf(A)).
function_d(_, nil-bintree(_):[]=>leaf(A):=>leaf(A)).
function_d(_, unfold-_ list:[]=>H::T:=>H::T).
function_d(_, unfold-pnat:[]=>s(N):=>s(N)).
function_d(_, unfold-_ tree:[]=>node(H, T):=>node(H, T)).
function_d(_, unfold-bintree(_):[]=>node(H, L, R):=>node(H, L, R)).
function_d(E, Rule:C=>E:=>R):-
	function_defn(E, Rule:C=>E:=>R).

function_d(_, nil-Type:[]=>Base:=>Base, [1], Type):-
	base_type(Type, Base).
function_d(_, unfold-Type:[]=>Term:=>Term, [1], Type):-
	con_type(Type, Term, _, _).
function_d(E, Rule:C=>E:=>R, _, _):-
	function_defn(E, Rule:C=>E:=>R).

/*
term_type(Vs, GroundTerm, Type):-
	member(GroundTerm:Type, Vs),!.
term_type(Vs, GroundTerm, Type):-
	GroundTerm =.. [F|_], \+ F = appn,
	recorded(theorem,theorem(F, eqn, A, B), C),
        matrix(_, _ in Type, A).
term_type(Vs, GroundTerm, Type):-
	GroundTerm =.. [appn, F, _],
	F =.. [F1|_],
	recorded(theorem,theorem(F1, eqn, A, B), C),
        matrix(_, _ in Type, A).
term_type(Vs, GroundTerm, Type):-
	GroundTerm =.. [appn, F, _], 
	F =.. [F1|List],
        F2 =.. [F1|[dummy|List]],
	data(F2, Type, _, _).
term_type(Vs, GroundTerm, Type):-
	data(GroundTerm, Type, Deps, _).
        list_type(Vs, Deps).
*/

list_type(_, []).
list_type(Vs, [H:Type|T]):-
	member(H:Type, Vs), !,
	list_type(Vs, T).
list_type(Vs, [H:Type|T]):-
	data(H, Type, Deps, _),
	append(T, Deps, NewT),
	list_type(Vs, NewT).


 gfp(X list, list_fun of X).
 gfp(pnat, suc_fun).
 gfp(int, suc_fun).
 gfp(bintree(X), bin_fun of X).
 gfp(_-eq, obs_fun).

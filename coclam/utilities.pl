/************************************************************
      File: utilities.pl

      Author: Louise Dennis

      Last Modified: 14th August 1997

      Description:  Utility Predicates for Coinduction Methods

      Predicates: generator/2
****************/

generator(Term, NewTerm):-
	Term =.. [GeneratorFunction|Alist],
	NewTerm =.. [C|ArgumentList],
	constr(C),
	\+ (member(X, Alist), exp_at(X,_,Constructor),
	                     \+var(Constructor), 
constr(Constructor)), 
	member(ModTerm, ArgumentList),
	exp_at(ModTerm, _, Mod),
	\+var(Mod),
	Mod =.. [GeneratorFunction|_].


/* 
map_list_history_filter(?OldList,?X-+OldElem:=>NewElem,+Pred,
?NewList,?Hist)
 * same as map_list_history/5 but elements for which Pred 
fails are skipped.  */
map_list_history_filter([],_,_,[],_).
map_list_history_filter([Oh|Ot], (X-Old):=>New, Pred,[Nh|Nt], Hist) :-
    copy_term([((X-Old)->New),Pred],[((X1-Old1)->New1),Pred1]),
    X1 = Hist, Old1=Oh,New1=Nh,Pred1,!,
    map_list_history_filter(Ot, (X-Old):=>New, Pred, Nt, [Nh|Hist]).
map_list_history_filter([_|Ot],(X-Old):=>New,Pred,Nt,Hist) :-
    map_list_history_filter(Ot,(X-Old):=>New,Pred,Nt,Hist).


delete_member(_, [], []).
delete_member(H, [H|T], NewT):-
	delete_member(H, T, NewT).
delete_member(X, [H|T], [H|NewT]):-
	\+ X == H,
	delete_member(X, T, NewT).

nel([H|_], 1, H).
nel([_|T], N, El):-
	\+ N = 1,
	N1 is N - 1,
	nel(T, N1, El).

sub_list([_|T], T).
sub_list([_|T], L):-
	sub_list(T, L).

merge([], List, List).
merge([H|T], List, Out):-
	\+ member(H, List),
	merge(T, [H|List], Out).
merge([H|T], List, Out):-
        member(H, List),
        merge(T, List, Out).
        
intersect([], _, []).
intersect([H|T], List, [H|Intersection]):-
	member(H, List),
	intersect(T, List, Intersection).
intersect([H|T], List, Intersection):-
	\+ member(H, List),
	intersect(T, List, Intersection).
	
length([], 0).
length([_|T], L):-
	length(T, N),
	L is N+1.
	
delete_all([], Set, Set).
delete_all([H|T], Set, FSet):-
	delete_member(H, Set, NewSet),
	delete_all(T, NewSet, FSet).

%% endmember(+List, -LastElementofList).
endmember(A, B):-
	reverse(B, Rev),
	member(A, Rev).

	
%% rep(+Term, -NewTerm, +Sublist).
%% Renames various subterms in Term in accordance with the
%% information in Sublist.
rep(Term, Term, []).
rep(Term, NewTerm, [[Hv1, Hv2]|Tail]):-
	replace_all(Hv2, Hv1, Term, RTerm),
	rep(RTerm, NewTerm, Tail).

sub_set([], []).
sub_set([H|T], [H|Out]):-
	sub_set(T, Out).
sub_set([_|T], Out):-
	sub_set(T, Out).
	
sub_set([], Set, Set).
sub_set([H|T], Set, Out):-
	sub_set(T, [H|Set], Out).
sub_set([_|T], Set, Out):-
	sub_set(T, Set, Out).
	
sub_set([], Set, Set, []).
sub_set([H|T], Set, Out, R):-
	sub_set(T, [H|Set], Out, R).
sub_set([H|T], Set, Out, [H|R]):-
	sub_set(T, Set, Out, R).

rem_list(_, [], []).
rem_list(A, [H|T], NewT):-
	member(H, A),
	rem_list(A, T, NewT).
rem_list(A, [H|T], [H|NewT]):-
	\+ member(H, A),
	rem_list(A, T, NewT).

%% dm(+Term, +NewTerm, -AnnTerm, -Substitutionlist)
%% This follows fairly closely David and Toby's difference  
%%matching
%% algorithm.  The main difference is that in the above  
%%predicates I
%% am trying to difference match a Coinduction Conclusion  
%%against the
%% original term (not the hypothesis).  This means some of the
%% variables don't match up (e.g. append(l1, l2) and  
%%append(v0::v1,
%% l2) - should l1 match with v0 or v1 ?).  As a result a small 
%%hack
%% has been put in to get round this - reversing the order  
%%variables
%% appear in (so l1 will be matched with v1).  An not insisting 
%%that
%% atomic terms be equal.
dm(A, B, C, D):-
	dm(A, B, C, [], D).
dm(Term, NTerm, Term, List, Out):-
	atomic(Term),
	atomic(NTerm),
	((\+ data(NTerm, _, _, non_rec),\+ data(Term,_,_,non_rec));
	                                 Term=NTerm),  
	(\+ (member([Term, XTerm], List), \+ XTerm=NTerm)),
	merge([[Term, NTerm]], List, Out).
dm(NewTerm, Term, AnnTerm, In, Out):-
	Term =.. [Functor|TermList],
	TermList \== [],
	NewTerm =.. [Functor|NewTermList],
	NewTermList \== [],
	dmlist(NewTermList, TermList, AnnTermList, In, SubstList),
	findset(S, member(S, SubstList), Out),
	AnnTerm =.. [Functor|AnnTermList].
dm(NewTerm, Term, AnnTerm, In, Subst):-
	Term =.. [FTerm|_],
	NewTerm =.. [FNewTerm|NewTermList],
	endmember(SubTerm, NewTermList),
	dm(SubTerm, Term, AnnSubTerm, In, Subst),
	strip_meta_annotations(NewTerm, NTerm),
	strip_meta_annotations(SubTerm, STerm),
	exp_at(NTerm, WHPos, STerm),
	\+ WHPos = [0|_],
	replace(WHPos, AnnSubTerm, NewTerm, PAnnTerm),
	wave_fronts(PAnnTerm, [[]-[WHPos]/[hard,out]], AnnTerm).

%% dmlist(+ListofNewTerms, +ListofOldTerms, -Annotatedlist,  
%%-ListofSubs)
%% Needed because of the breakdown of functions into functors  
%%and
%% arguement lists.
dmlist([], [], [], List, List).
dmlist([NewH|NewTail], [H|Tail], [AnnH|AnnTail], In, Slist):-
	dm(NewH, H, AnnH, In, SListH),
	dmlist(NewTail, Tail, AnnTail, SListH, Slist).
	
%% Difference matching with function substitution for universally
%% quantified functions  
dm_vs(A, B, C, D, Vs):-
	dm_vs(A, B, C, [], D, Vs).
dm_vs(Term, NTerm, Term, List, Out, _):-
	atomic(Term),
	atomic(NTerm),
	((\+ data(NTerm,_,_,non_rec),\+ data(Term,_,_,non_rec)); Term=NTerm),
	(\+ (member([Term, XTerm], List), \+ XTerm=NTerm)),
	merge([[Term, NTerm]], List, Out).
dm_vs(NewTerm, Term, AnnTerm, In, Out, Vs):-
	Term =.. [Functor|TermList],
	TermList \== [],
	NewTerm =.. [Functor|NewTermList],
	NewTermList \== [],
	dm_vslist(NewTermList, TermList, AnnTermList, In, SubstList, Vs),
	findset(S, member(S, SubstList), Out),
	AnnTerm =.. [Functor|AnnTermList].
dm_vs(NewTerm, Term, AnnTerm, In, Subst, Vs):-
	Term =.. [FTerm|_],
	NewTerm =.. [FNewTerm|NewTermList],
	endmember(SubTerm, NewTermList),
	dm_vs(SubTerm, Term, AnnSubTerm, In, Subst, Vs),
	strip_meta_annotations(NewTerm, NTerm),
	strip_meta_annotations(SubTerm, STerm),
	exp_at(NTerm, WHPos, STerm),
	\+ WHPos = [0|_],
	replace(WHPos, AnnSubTerm, NewTerm, PAnnTerm),
	wave_fronts(PAnnTerm, [[]-[WHPos]/[hard,out]], AnnTerm).
dm_vs(NewTerm, Term, AnnTerm, In, Out, Vs):-
	Term =.. [Functor|TermList],
	NewTerm =.. [NewFunctor|NewTermList],
	member(NewFunctor:_, Vs),
	dm_vslist(NewTermList, TermList, AnnTermList, In, SubstList, Vs),
	findset(S, member(S, [[NewFunctor, Functor]|SubstList]), Out),
	AnnTerm =.. [NewFunctor|AnnTermList].


%% dm_vslist(+ListofNewTerms, +ListofOldTerms, -Annotatedlist,  
%%-ListofSubs)
%% Needed because of the breakdown of functions into functors  
%%and
%% arguement lists.
dm_vslist([], [], [], List, List,_).
dm_vslist([NewH|NewTail], [H|Tail], [AnnH|AnnTail], In, Slist, Vs):-
	dm_vs(NewH, H, AnnH, In, SListH, Vs),
	dm_vslist(NewTail, Tail, AnnTail, SListH, Slist, Vs).

%% difference matching with base cases.
dm_vs_base(A, B, C, D, Vs):-
	dm_vs_base(A, B, C, [], D, Vs).
dm_vs_base(Term, NTerm, Term, List, Out, _):-
	atomic(Term),
	atomic(NTerm),
	(data(Term,_,_,non_rec); Term=NTerm),
	(\+ (member([XTerm, NTerm], List), \+ Term=XTerm)),
	merge([[Term, NTerm]], List, Out).
dm_vs_base(NewTerm, Term, AnnTerm, In, Out, Vs):-
	Term =.. [Functor|TermList],
	TermList \== [],
	NewTerm =.. [Functor|NewTermList],
	NewTermList \== [],
	dm_vs_baselist(NewTermList, TermList, AnnTermList, In, SubstList, Vs),
	findset(S, member(S, SubstList), Out),
	AnnTerm =.. [Functor|AnnTermList].
dm_vs_base(NewTerm, Term, AnnTerm, In, Subst, Vs):-
	Term =.. [FTerm|_],
	NewTerm =.. [FNewTerm|NewTermList],
	endmember(SubTerm, NewTermList),
	dm_vs_base(SubTerm, Term, AnnSubTerm, In, Subst, Vs),
	strip_meta_annotations(NewTerm, NTerm),
	strip_meta_annotations(SubTerm, STerm),
	exp_at(NTerm, WHPos, STerm),
	\+ WHPos = [0|_],
	replace(WHPos, AnnSubTerm, NewTerm, PAnnTerm),
	wave_fronts(PAnnTerm, [[]-[WHPos]/[hard,out]], AnnTerm).
dm_vs_base(NewTerm, Term, AnnTerm, In, Out, Vs):-
	Term =.. [Functor|TermList],
	NewTerm =.. [NewFunctor|NewTermList],
	member(NewFunctor:_, Vs),
	dm_vs_baselist(NewTermList, TermList, AnnTermList, In, SubstList, Vs),
	findset(S, member(S, [[NewFunctor, Functor]|SubstList]), Out),
	AnnTerm =.. [NewFunctor|AnnTermList].


%% dm_vs_baselist(+ListofNewTerms, +ListofOldTerms, -Annotatedlist,  
%%-ListofSubs)
%% Needed because of the breakdown of functions into functors  
%%and
%% arguement lists.
dm_vs_baselist([], [], [], List, List,_).
dm_vs_baselist([NewH|NewTail], [H|Tail], [AnnH|AnnTail], In, Slist, Vs):-
	dm_vs_base(NewH, H, AnnH, In, SListH, Vs),
	dm_vs_baselist(NewTail, Tail, AnnTail, SListH, Slist, Vs).


replace_universal_vars(Vars,Term,NewTerm, Meta_types) :-
    untype(Vars,Vs,Types), zip(VsNewVs,Vs,Meta),  zip(Meta_types, Meta, Types),
    replace_universal_vars_1(VsNewVs,Term,NewTerm).

scheme_type(_, [_-_-nothing], either):-!.
scheme_type(_, [_-_-(unfold-_)], step):-!.
scheme_type(_, [_-_-(nil-_)], base):-!.
scheme_type(Vs, [E-_-Rule], base):-
	replace_universal_vars(Vs, E, LE),
	copy_term(LE, LE2),
	exp_at(LE, Pos, Var),
	var(Var),
	function_defn(LE2, Rule:_=>LE2:=>_),
	exp_at(LE2, Pos, Term),
	\+var(Term),
	atomic(Term), !.
scheme_type(Vs, [E-_-Rule], step):-
	replace_universal_vars(Vs, E, LE),
	copy_term(LE, LE2),
	exp_at(LE, Pos, Var),
	var(Var),
	function_defn(LE2, Rule:_=>LE2:=>_),
	exp_at(LE2, Pos, Term),
	\+ var(Term),
	\+ atomic(Term).
scheme_type(Vs, [E-_-Rule], step):-
	replace_universal_vars(Vs, E, LE),
	copy_term(LE, LE2),
	\+ (exp_at(LE, Pos, Var),
	    var(Var),
	    function_defn(LE2, Rule:_=>LE2:=>_),
	    exp_at(LE2, Pos, Term),
	    \+ var(Term)).


%% Expression at Pos2 is contained in the expression at Pos1
my_subterm(Pos1, Pos2):-
	reverse(Pos1, Pos1R),
	reverse(Pos2, Pos2R),
	sterm(Pos1R, Pos2R).

sterm([], _).
sterm([H|T1], [H|T2]):-
	sterm(T1, T2).


%% remove_uninstantiated/2 removes any uninstantiated variables that appear 
%% in the list.  These appear as left overs from the lift, rewrite, ground
%% process undertaken in the various lookahead predicates.
remove_uninstantiated([], []).
remove_uninstantiated([V:T|Tl], [V:T|Ntl]):-
	ground(V), \+ data(V, T, _, non_rec),
	remove_uninstantiated(Tl, Ntl).
remove_uninstantiated([V:_|Tl], Ntl):-
	var(V),
	remove_uninstantiated(Tl, Ntl).
remove_uninstantiated([V:Ty|Tl], Ntl):-
	data(V, Ty, L, non_rec),
	append(L, Tl, NewTail),
	remove_uninstantiated(NewTail, Ntl).

reverse_dl([], X-X).
reverse_dl([H|T], Y-Z):-
	reverse_dl(T, Y-[H|Z]).





change_hyps(Plan, Addr, H):-
	node(Plan, NewAddr, []==>Gl, S1, S2, S3, S4, S5).
change_hyps(Plan, Addr, H):-
        node(Plan, NewAddr, Hl==>Gl, S1, S2, S3, S4, S5),
	\+ Hl = [],
        retract(node(Plan, NewAddr, Hl==>Gl, S1, S2, S3, S4, S5)),
        assertz(node(Plan, NewAddr, H==>Gl, S1, S2, S3, S4, S5)).

%% one position is a 

var_in_wave_front(Vars, Exp, WHPos, EPos):-
	member(V:_, Vars),
	exp_at(Exp, VarPos, V),
	append(VarPos, EPos, NewPos),
	\+ (member(WH, WHPos), my_subterm(WH, NewPos)).

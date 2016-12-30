/* * Yet, another wave-rule parser. 
 *
 * Clam3.2 comes with a wave-rule parser which gets easily
 * overwheelmed by the combinatorial explossion, even if input
 * moderately big formulae. Ian Green suggested it could be 
 * improved by adopting his search space pruning strategies for 
 * dynamic rippling. Basically, rather than generating all 
 * possible annotations before checking both skeleton 
 * preservation, and maximun orientation, it uses the skeleton 
 * of one possible annotation of either side of a given 
 * equation/implication to calculate the annotatations of the 
 * other side. This significantly speeds-up wave-rule generation. 
 * For example, from 
 *
 *     ctr( s(n) ) = rest( parll( rel( cell,    f1 ),
 *				  rel( ctr( n ),f2 )
 *			         ), l
 *		          ) 
 *
 * this wave-rule parser gets the only possible rule in less than 
 * 2 secs. On the other hand, it took clam3.2's parser 1 Hr, 25 
 * mins, and 31 secs to do the same job. 
 *
 * Files needed.
 *
 */

/* LD. Altered slightly to allow All Possible annotation on both sides
 * of the rule.  The original code only annotated the LHS with
 * outward wave fronts - so no rippling in!!!! */
add_wave_rule(RuleName,equ(D)) :-
    writef(' adding wave-rules for %t:', [RuleName]),
    %% Pick one rewrite rule derived from RuleName
    pick_a_rule(RuleName,C=>Rule,equ(D),Vars),
	%% Changed to equational rewrites only to speed up loading.
    getargs(Rule,LHS,RHS),
    %% Get one possible annotation for the LHS
    ground_difference_unify_and_some(split,_,LHS,RHS,ALHS,_),
    %% This is where Ian's code come to life. Given one possible 
    %% LHS annotatation, it calculates the corresponding 
    %% (maximally oriented) annotations for the RHS.
    superimpose(direction_in_or_out,ALHS,LHS,RHS,ARHS),
    %% 
    adjust_orient_rhs(C=>ALHS:=>ARHS,TheGroundRule),
    wave_rule_type(TheGroundRule,Type),
    TypeDir=..[Type,equ(D)],
    replace_universal_variables(Vars,TheGroundRule,TheRuleSchema),
    writef('.'),
    uniq_recorda(wave,wave(RuleName,TheRuleSchema,TypeDir),_).

maplist(Pred, Ws, Xs, Ys, Zs) :-
        map_list_(Ws, Xs, Ys, Zs, Pred).

map_list_([], [], [], [], _).
map_list_([W|Ws], [X|Xs], [Y|Ys], [Z|Zs], Pred) :-
        call(Pred, W, X, Y, Z),
        map_list_(Ws, Xs, Ys, Zs, Pred).

ground_difference_unify_and_some(Type, Skel, Hyp, Goal, NewHyp, NewGoal):-
	ground_difference_unify(Type, Skel, Hyp, Goal, NewHyp, NewGoal).
ground_difference_unify_and_some(Type, Skel, Hyp, Goal, OutHyp, NewGoal):-
	ground_difference_unify(Type, Skel, Hyp, Goal,	NewHyp, NewGoal), 
	wave_fronts(UNAnn, Wave_fronts, NewHyp),
	gdu(UNAnn, Wave_fronts, OutHyp).
gdu(UnAnn, Wave_fronts, OutHyp):-
	change_in(Wave_fronts, WFIn, same),
	wave_fronts(UnAnn, WFIn, OutHyp).
gdu(UNAnn, Wave_fronts, OutHyp):-
	change_in(Wave_fronts, WFIn, same),
	gdu(UNAnn, WFIn, OutHyp).

change_in([], [], changed).
change_in([WF-WHList/[hard, out]|Tail], [WF-WHList/[hard,
	in]|NewTail], _):-
	change_in(Tail, NewTail, changed).
change_in([H|T], [H|NT], C):-
	change_in(T, NT, C).

ground_difference_unify(Type,Skel,Hyp,Goal,NewHyp,NewGoal) :-
    embedding_ground(E1,Skel,Goal),
    embedding_ground(E2,Skel,Hyp),
    regular_form(Type,NewGoal,aterm(Skel,Goal,E1)),
    regular_form(Type,NewHyp,aterm(Skel,Hyp,E2)).

embedding_ground(E,T1,T2) :-
    embedding_ground(E,T1,T2,[],[]).
embedding_ground([Addr1-Addr2],Var,Atom,Addr1,Addr2) :-
    atomic(Atom),
    Var = Atom,!.
embedding_ground([Addr1-Addr2],Var,'@sink@'(Term),Addr1,Addr2) :-
    Var = '@sink@'(Term),!.
embedding_ground([Addr1-Addr2|Mapping], Term1,Term2,Addr1,Addr2) :-
    \+ atomic(Term2),
    Term2 =.. [F|Args2],			%term2 is ground
    /* decompose Term1 into a skeletal functor for F if Term1 is a var */
    length(Args2,N),length(Args1,N),
    Term1 =.. [F|Args1],
    embedding_ground_list(Mapping,Args1,Args2,Addr1,Addr2,1).
embedding_ground(Map,Term1,Term2,Addr1,Addr2) :-
    \+ var(Term2),
    Term2 =.. [_F2|Args2],
    nth(N,Args2,Arg2),
    embedding_ground(Map,Term1,Arg2,Addr1,[N|Addr2]).

embedding_ground_list([],[],[],_,_,_).
embedding_ground_list(Ms,[A1|A1s],[A2|A2s],Pos1,Pos2,N) :-
    embedding_ground(M,A1,A2,[N|Pos1],[N|Pos2]),
    NN is N + 1,
    embedding_ground_list(Mss,A1s,A2s,Pos1,Pos2,NN),
    append(M,Mss,Ms).

regular_form(Type,Term,aterm(_Skel,Erasure,Em)) :-
    regular_form(Type,hole,[],Term,Erasure,Em).
regular_form(Type,front,Pos,'@wave_var@'(Hole),Erasure,Em) :-
    member(_-Pos,Em),!,
    /* we are looking at a node in Erasure which is part of the skeleton,
     * and we are currently in a front, so add a wave-hole
     */	
    Erasure =.. [F|Eargs],
    regular_form_map(Type,1,hole,Pos,Holes,Eargs,Em),
    Hole =.. [F|Holes].
regular_form(Type,hole,Pos,'@wave_front@'(hard,out,Front),Erasure,Em) :-
    \+member(_-Pos,Em),!,
    /* we are looking at a node in Erasure which is part of the front,
     * and we are currently in a hole, so add a wave-front
     */	
    Erasure =.. [F|Eargs],
    regular_form_map(Type,1,front,Pos,Fronts,Eargs,Em),
    Front =.. [F|Fronts].

/* anything else just recurse */
regular_form(split,hole,Pos,Term,Erasure,Em) :-
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,hole,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form(split,front,Pos,
	     '@wave_var@'('@wave_front@'(hard,out,Term)),Erasure,Em) :-
    %% Only add anntotation here if there is some of the skeleton
    %% below this place in the term tree.
    member(_-HolePos,Em),
    append(_,Pos,HolePos),!,
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,front,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form(split,front,Pos,Term,Erasure,Em) :-
    %% otherwise, we are in a front and there are no holes below Pos
    Erasure =.. [F|Eargs],
    regular_form_map(split,1,front,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].

regular_form(merged,Kind,Pos,Term,Erasure,Em) :-
    Erasure =.. [F|Eargs],
    regular_form_map(merged,1,Kind,Pos,Terms,Eargs,Em),
    Term =.. [F|Terms].
regular_form_map(_Type,_,_Kind,_Pos,[],[],_Em).
regular_form_map(Type,N,Kind,Pos,[H|Holes],[E|Eargs],Em) :-
    regular_form(Type,Kind,[N|Pos],H,E,Em),
    NN is N + 1,
    regular_form_map(Type,NN,Kind,Pos,Holes,Eargs,Em).
    


somechk(Pred, [X|_]) :-
        call(Pred, X), !.
somechk(Pred, [_|Xs]) :-
        somechk(Pred, Xs).


       % partition(?List, ?N, ?PreN, ?Nth, ?PostN): splits List up in 3 parts:
        % elements 0 to N-1, the Nth element, and elements N+1 to end.
        % Fail if N>=length(List).
        % Notice that all arguments can be uninstantiated (at the cost
        % of tail-recursion....who said more "declarative" algorithms are
        % also more efficient? Richard O'Keefe, where are you when we
        % could prove you wrong?)
partition([H|T], 0, [], H, T).
partition([H|T], N, [H|Pre], Nth, Post) :-
    partition(T, M, Pre, Nth, Post),
    N is M+1.






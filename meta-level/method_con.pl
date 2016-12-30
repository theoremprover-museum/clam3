/*
 * This file contains the connectives that can be used in the
 * method-language. The predicates  that can be used in the
 * method-language live in the file method-pred.pl.
 */

/*
 * All the operator declarations for the newly defined meta-linguistic
 * connectives live in util.pl. This is to allow them to be used
 * befeore the are defined.
 */

        % Hide meta-linguistic negation as Prolog's negation by failure
        % and meta-linguistic disjunction as Prolog's backtrackable ';'.
        % Some of these connectives are purely cosmetic predicates. (Am
        % I taking this too far?). 
        % (Realise that we are already using Prolog's conjunction ',' as
        % our meta-linguistic conjunction).
        %
        % or/2 is already defined by Oyster, so we use 'v' as
        % meta-linguistic disjunction.
G1 v _  :- G1.
_  v G2 :- G2.

        % G1 orelse G2 will execute G1 but if this fails will execute
        % G2. The only difference between "G1 orelse G2" and" G1 ; G2"
        % is that the orelse construct does not allow backtracking over
        % G1. Thus, "G1 orelse G2" is shorthand for "(G1,!);G2" or
        % equivalently "G1->true;G2".
        % We call this connective "committed disjunction" for obvious
        % reasons. 
G1 orelse _  :- G1,!.
_  orelse G2 :- G2.

        % G1 andpossibly G2. The "andpossibly" connective is like
        % conjuntion: it tries to satisfy G1 and G2. If this cannot be
        % done, it tries to satisfy G1 alone. Thus, a sequence
        % G1 andpossibly ... andpossibly Gn will try to satisfy
        % G1,...,Gi for decreasing i from n to 1.
        %
        % NOTE: In a sequence G1,...,Gn, satisfying G1,..Gi with i<n
        % means that Gi+1,...,Gn must be false.
        % EXAMPLE:
        %       :- member(X,[1,15,25,3]) andpossibly X>10 andpossibly X>20
        % succeeds with
        %       X=25, X=15, X=1, X=3 in this order.
       %
        % NOTE that this connective has no declarative semantics, only a
        % procedural one. 
G1 andpossibly G2 :- G1,G2.
G1 andpossibly G2 :- G1, \+ G2.

        % map_list(?OldList,+OldElem:=>NewElem,+Pred,?NewList) maps
        % OldList into NewList by applying Pred to each element. OldElem
        % and NewElem must occur in Pred, and are regarded as input- and
        % output-argument respectively. If Pred is bidirectional, then
        % maplist works bidirectionally as well.
        % Example:
        %     :- maplist([1,2,3],I:=>O,O is I+10,L).
        % gives L=[11,12,13].
        % More subtle use of the (I->O) pattern is also possible:
        %     :- maplist([a+1,b+2,c+3],C+N:=>C+NN,NN is N+10,L).
        % gives L=[a+11,b+12,c+13]
        %
        % This maplist/4 is somewhat more general than the maplist/3
        % from the Quintus library, since that requires Pred to be
        % 2-place, namely Pred(Old,New).
map_list([],_,_,[]).
map_list([Oh|Ot],Old:=>New,Pred,[Nh|Nt]) :-
    copy([(Old->New),Pred],[(Old1->New1),Pred1]),
%    copy([(Old->New),Pred],[(Old2->New2),Pred2]),    
% I think this double copying is redundant.
    Old1=Oh,New1=Nh,Pred1,
    map_list(Ot,Old:=>New,Pred,Nt).

        % begin_guard(-ID), end_guard(+ID), guard_ended(+ID) 
        % Meta-programming predicates to allow code to distinguish
        % some ``guard'' condition failing on backtrakcing, or never
        % succeeding.  The iterate connective below gives an exmple of
        % use.

begin_guard( Id ) :-
        uniq_id( Id ),
        ( asserta( 'guard mark'( Id ) ) ; retractall( 'guard mark'( Id ) ), !, fail ).
guard_ended(Id) :-
        \+ clause( 'guard mark'( Id ), true ).
end_guard( Id ) :-
        retractall( 'guard mark'( Id ) ).

iterate( Arg, Cur:=>Next, Pred, Inv, Res ) :-
            copy( [Cur,Next,Pred,Inv], [Cur1,Next1, Pred1, Inv1] ),
            Arg = Cur1,
            begin_guard( GId ),
            ( true ; guard_ended( GId ),!, fail ), 
            Pred1,
            end_guard( GId ),
            ( Inv1, !, iterate( Next1, Cur:=>Next, Pred, Inv, Res ) ;
	      Next1 = Res
            ).
iterate( Res, _, _, _, Res ).

repeat( [SG|RestSG], Cur:=>NextL, Tac, Pred, [SGTac|RestTacs], ResL ) :-
    copy( f(Cur,NextL,Tac,Pred), f(Cur1,NextL1,Tac1, Pred1) ),
    SG = Cur1,
    Pred1,
    repeat( NextL1, Cur:=>NextL, Tac, Pred, SGResTacs, SGResL ),
    append( SGResL, RestResL, ResL ),
    tac_tree( Tac1, SGResTacs, SGTac ),
    repeat( RestSG, Cur:=>NextL, Tac, Pred, RestTacs, RestResL ).
repeat( [SG|RestSG], Map, Tac, Pred, [idtac|RestTacs], [SG|RestResL] ) :-
    repeat( RestSG, Map, Tac, Pred, RestTacs, RestResL ).
repeat( [], _, _, _, [], []).

tac_tree( Tac, [], Tac ).
tac_tree( Tac, [idtac], Tac ) :- !.
tac_tree( Tac, [H|T], Tac then [H|T] ).


        % Bounded universal quantification construct, extensional variant:
        % forall {Var\List}: Pred succeeds if Pred succeeds for each
        % element of List. Var can occur in Pred.
        %
        % Notice that this succeeds with any Pred for empty Lists.
        %
        % Notice that all variables mentioned in Pred other than Var
        % will remain unbound.
        %       
        % We use double negation to avoid binding variables, 
forall {_ \ []}:_.
forall {Elem \ [L|Ls]}:Pred :-
    \+ \+ (Elem = L, Pred),
%   copy([Pred,Elem],[NewPred,NewElem]),
%   NewElem = L, NewPred,
    forall {Elem \ Ls}:Pred.

        % Bounded universal quantification construct, intensional variant:
        % forall {Var\Set}:Pred succeeds when Pred holds for all Var in
        % Set. Just convert Set to list of Values of Set, and call the
        % extensional variant to do the work.
        %
        % NOTE: if Set is the empty-set, then forall{V\Set}:Pred
        % succeeds for any Pred.  
        %
        % Notice that all variables mentioned in Pred other than Var
        % will remain unbound outside the evaluation of Set, and that
        % all variables (including Var), will remain unbound after
        % evaluation of the call to forall.
forall {Var\Set}:Pred :-
    \+ functorp(Set,.,2),
    Set\=[],
    findall(Var,Set,ValList),
    forall {Var \ ValList}:Pred.

        % Bounded existential quantification construct, intensional variant:
        % thereis {Var\Set}:Pred succeeds if there is binding for Var in Set
        % such that Pred is true. Var becomes bound to the first such
        % value, but we don't look for other values on backtracking.
        % Just compute values of Set and call extensional predicate to
        % do the work.
        % Minor variation is thereis {Var}:Pred (first clause below).
        % 
        % Can NOT be used in backtracking to generate all such elements
        % in List. If needed, remove cut in first clause.
        % 
        % Notice that all variables mentioned in Pred other than Var
        % will remain unbound outside the evaluation of Set.
thereis {Var}:Pred :- \+ functorp(Var,\,2),!,
    copy([Var,Pred],[NewVar,NewPred]), NewPred, !, NewVar=Var.
thereis {Var \ Set}:Pred :-
    \+ functorp(Set,.,2),
    Set\=[],
    findall(Var,Set,ValList),
    thereis {Var\ValList}: Pred.

        % Bounded existential quantification construct, extensional variant:
        % thereis {Var\List}: Pred succeeds if there is at least one
        % elem of List for which Pred succeeds. Var can of course occur
        % in Pred, and becomes bound to the first such element in List.
        % 
        % Can NOT be used in backtracking to generate all such elements
        % in List. If needed, remove cut in first clause.
        % 
        % Notice that all variables mentioned in Pred other than Var
        % will remain unbound.
thereis {Var\[Var|_]}: Pred :-  \+ \+ Pred,!.
thereis {Var\[_|Ls]}: Pred :- thereis {Var\Ls}: Pred.

        % findset/3 is as setof/3, except that it does not fail, but
        % succeeds with an empty list. Thus, in this respect it is like
        % findall/3, except that it does not return multiple solutions
        % (after all, it is like setof/3).

findset(A,B,C) :-
    findall(A,B,RC),
    sort(RC,C).

	% listof/3 is as setof/3, except that it does not fail, but
	% succeeds with an empty list. Thus, in this respect it is like
	% findall/3, except that it does not return multiple solutions
	% (after all, it is like setof/3).
listof(T,C,L) :- setof(T,C,L),!.
listof(_,_,[]).

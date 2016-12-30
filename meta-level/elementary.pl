
/*
 * This file contains a procedure to detect simple theorems.
 * It uses some (ie not exhaustive) propositional reasoning,
 * knows that equality is reflexive, can strip off universal
 * quantifiers, realises that 0 =/= s(X), nil =/= H::T,
 * tries to deal with existential goals.
 * It is intended to be a cheap test (compared to "propositional").
 * 
 * Stolen/borrowed/gratefully received from AlanS. Renamed some of the
 * predicates and variables, and re-ordered some of the code. 
 *
 * The crucial predicates are elementary/2 for the calculation of a
 * tactic that will prove a goal, and elementary/1 for the execution of it.
 */

        % elementary(+Sequent,?Tactic) will compute Tactic that will prove
        % Sequent, provided Sequent is a propositional elementary.
        % 
        % We have two clauses for elementary/2, one to stick in the
        % hyp-list if not already provided, and one if hyp-list is
        % already provided. In both cases elementary/2 calls elementary/3
        % to find tactic for sequent H==>G given a list of hyps
        % previously elim'd.
elementary( H==>[V:G|Gs],[Tactic|Tactics]) :-
    var(V),
    !,
    elementary0( H==>G, Tactic, V ),
    elementary( H==>Gs,Tactics ).
elementary( H==>[_:G|Gs],[Tactic|Tactics]) :-
    !,
    elementary0( H==>G, Tactic, _ ),
    elementary( H==>Gs,Tactics ).
elementary( H==>[G|Gs],[Tactic|Tactics]) :-
    !,
    elementary0( H==>G, Tactic, _ ),
    elementary( H==>Gs,Tactics ).
elementary( _==>[], [] ) :- !.


elementary([]==>G,Tactic) :- hyp_list(H),
                             strip_meta_annotations(G,NewG),
                             elementary0(H==>NewG,Tactic,_).
elementary([H|Hs]==>G,Tactic) :- 
                             strip_meta_annotations(G,NewG),
                             elementary0([H|Hs]==>NewG,Tactic,_).

        % elementary/3 looks for simplified rule that is applicable,
        % checks that it has not been used before, adds it to list of
        % hyps elim'd, finds recursively tactics for each of the
        % subgoals, and combines tactics to form overall tactic.
elementary0(H==>G,Tactic,Wit) :- 
    prule(H==>G,Rule,Sublist,Wit),
    elementarylist(H,Sublist,Tacticlist),
    newelementary(Tactic,Rule,Tacticlist).

        % elementarylist/4 finds tactics for each of list of sequents, in
        % presence of hypothesis list H (these lists are stored
        % incrementally in rules, so we have to use update/3 to find
        % full hyp list for subgoals). 
elementarylist(_,[],[]):- !.
elementarylist(H,[Subseq,Wit],[Subtactic]) :- !,
    update(H,Subseq,Subgoal),
    elementary0(Subgoal,Subtactic,Wit),!.
elementarylist(H,[H1,W1|T1],[H2|T2]) :- 
    elementarylist(H,[H1,W1],[H2]),
    elementarylist(H,T1,T2).

newelementary(Rule,Rule,[]) :- !.
newelementary(intro(left) then [Subtact,wfftacs],intro(left),[Subtact]):-
    !.
newelementary(intro(right)then [Subtact,wfftacs],intro(right),[Subtact]):-
    !.
newelementary(intro then [Subtact,wfftacs],intro(a),[Subtact]) :- !.
newelementary(intro(new N) then [Subtact,wfftacs],intro(new N),[Subtact]) :- !.
newelementary(Rule then Subtact,Rule,[Subtact]) :- !.
newelementary(Rule then Tacticlist,Rule,Tacticlist).

update(H,(HH==>GG),(K==>GG)) :- !,
    append(H,HH,K).
update(H,(==> GG),(H==>GG)).

        %  prule/3 is simplified version of NurPRL rule/3 with arguments
        %  (Rule,Sequent,Subgoal).  Special rule (wfftacs) for wf-goals.
prule(H==>X in T,hyp(X), [], axiom ) :-
    ( atom(X),! ; var(X) ),
    hyp(X:TT,H),
    convertible(T,TT).
prule(H==>A in T, hyp(X),  [], axiom ) :-
    \+ A = ( _ = _ ),
    hyp(X:HT,H),
    ( HT = (AA=_ in TT); HT =(_=AA in TT)),
    convertible(T,TT),
    convertible(A,AA).
prule( H==>T, hyp(X),[], X ) :-
    functor( T,F, A ),
    functor( P,F, A ),
    hyp(X:P,H),
    convertible(T,P).
prule(_==>G in u(_),wfftacs,[], wfftacs ) :- \+ functor(G,=,2).

        % to avoid needing identity method as well:
prule(_==>T in _,identity,[], axiom ) :-
      nonvar(T), T = (X=X),!.

prule(_==>T, clam_arith, [], axiom) :-
      nonvar(T), T = (X < Y => void),
      pnat2nat(X, NX),
      pnat2nat(Y, NY),
      \+ NX < NY,!.
prule(_==>T, clam_arith, [], axiom) :-
      nonvar(T), T = (X < Y),
      pnat2nat(X, NX),
      pnat2nat(Y, NY),
      NX < NY,!.
prule(_==>T, clam_arith, [], axiom) :-
      nonvar(T), T = (greater(X,Y) => void),
      pnat2nat(X, NX),
      pnat2nat(Y, NY),
      NX =< NY,!.
prule(_==>T, clam_arith, [], axiom) :-
      nonvar(T), T = greater(X,Y),
      pnat2nat(X, NX),
      pnat2nat(Y, NY),
      NX > NY,!.
prule(_==>T, clam_arith, [], axiom) :-
      nonvar(T), T = (X = Y in _ => void),
      pnat2nat(X, NX),
      pnat2nat(Y, NY),
      \+ NX = NY,!.
        % I know this is supposed to be a >*propositional*< decider, but
        % it's useful to just strip off the universal vars, and see if
        % we are left with a propositional elementary:
prule(_==>{true},istrue,[], unit) :- !.
prule(_==>j({true}),istrue,[], unit) :- !.
prule(H==>j(B),jwittac(W),[],W) :- jdecide(B,H,W).
prule(H==>nj(B),njwittac(W),[], W ) :- njdecide( B, H, W).

        % We have to compensate for Oyster's braindamaged arithmetic
        % somewhere. These are the bare bones of what one would expect...:
prule(H==>_,clam_arith,[], void_derive(N)) :- 
     hyp( N:L=R in pnat, H ), 
     ground(L-R),
     memberchk(L-R,[s(_)-0,0-s(_),s(X)-X,X-s(X)]),
     !.
	% A.Ireland: hard-wired unquiness property 
        % for list constructors. 
prule(H==>_,clam_arith,[], void_derive(N)) :-
     hyp( N:L=R in _ list, H ),
     ground(L-R),
     memberchk(L-R,[(_::_)-nil,nil-(_::_)]),
     !.

prule(H==>_ ,elim(X),[], X):- hyp(X:void,H),!.
prule(H==>_, isfalse(X),[], X):- hyp(X:j({false}),H),!.

prule(_==>V:T=>G,dequantify_once,[[V:T]==>G,W], lambda(V,W) ) :- !.
        % int is used as "true" in definitions (e.g. even, leq, etc):
prule(H==>A=>B,intro(new [Y]),[[Y:A]==>B,W ], lambda(Y,W) ):- hfree([Y],H),!.
prule(_==>A#B, intro, [==>A,W1, ==>B, W2], (W1&W2) ) :- !.
prule(_==>V:A#B,intro(on(W1)),[==>A,W1,==>B,W2], (W1&W2)) :-
    var(V),
    !.
prule(_==>V:A#B,intro(on(W1)),[==>A,W1,==>Bs,W2], (W1&W2)) :-
    nonvar(V),
    s( B, [W1], [V], Bs ),
    !.
prule(H==>T,elim(Z),[[U:A,V:B,W:dummy,elim(Z)]==>T,W1], spread(Z,[U,V,W1])):-
    hyp(Z:A#B,H),\+ hyp(elim(Z),H),hfree([U,V,W],H),!.
prule(H==>T,elim(Z),[[U:A,V:BU,W:dummy,elim(Z)]==>T,W1], spread(Z,[U,V,W1])):-
    hyp(Z:(VV:A#B),H),
    \+ hyp( elim(Z), H ),
    s(B,[VV],[U],BU),
    hfree([U,V,W],H),
    !.
prule(H==>T, elim(V),
    [ [X:A ,N1:dummy, elim(V)]==>T, W1,
      [Y:B ,N2:dummy, elim(V)]==>T, W2 ], decide(V,[X,W1], [Y,W2]) ):-
          hyp(V:A\B,H),
          \+ hyp(elim(V),H),
          hfree([X,Y,N1,N2],H),
   !.
prule(_==>A\_ ,intro(left), [==>A,W], inl(W)).
prule(_==>_\B ,intro(right),[==>B,W], inr(W)).

prule(H==>G,elim(F),[[elim(F)]==>A, W,
                      [Y:void]==>G , _ ], F of W):-
    hyp(F:A=>void,H),
    \+ hyp(elim(F),H),
    hfree([Y],H).
prule(H==>_, contradiction(X,Y), [], contradict(X,Y) ) :- 
     hyp( X : j(A), H), 
     hyp(Y:nj(A),H),
     !.

jdecide( Bool, Hyps, X ) :- hyp(X:j(Bool), Hyps ),!.

jdecide(and(Bool1,Bool2), Hyps, jand_i(W1,W2) ) :-
     !,
     jdecide(Bool1, Hyps, W1 ),
     jdecide(Bool2, Hyps, W2 ),
     !.
jdecide(not(Bool), Hyps, jnot_i(W) ) :-
     !,
     njdecide(Bool,Hyps,  W ),
     !.
jdecide(or(Bool,_), Hyps, jor_il(W) ) :-
     !,
     jdecide(Bool,Hyps, W ),
     !.
jdecide(or(_,Bool), Hyps,  jor_ir(W) ) :-
     !,
     jdecide(Bool,Hyps,  W ),
     !.
/*
 * The following two clauses are required 
 * for Andrew Stevens datatype shell mechanism.
 * 
jdecide(Recog,_, unit ) :-
     Recog =.. [RName|Args],
     last(Arg,Args),
     functor(Arg,CName,_),
     tuple( shell_constructor, [CName, RName|_] ),
     !.

jdecide(Recog,Hyps, mutex( WitList ) ) :-
     tuple( shell, [Type,_,_,_,_,_,Recogs] ),
     select(Recog, Recogs, RestRecogs ),
     !,
     \+ member( mutex(Type), Hyps ),
     njdecide_list( RestRecogs, [mutex(Type)|Hyps], WitList ). 
 *
 */

jdecide_list( [H|T], Hyps, [HW|TW] ) :-
    jdecide( H, Hyps, HW ),
    jdecide_list( T, Hyps, TW ).
jdecide_list( [], _, [] ).

njdecide( Bool, Hyps, X ) :- hyp(X:nj(Bool), Hyps ),!.
     
njdecide(or(Bool1,Bool2), Hyps,  nor_i(W1,W2) ) :-
     !,
     njdecide(Bool1, Hyps, W1 ),
     njdecide(Bool2, Hyps, W2 ),
     !.
njdecide(not(Bool), Hyps, nnot_i(W) ) :-
     !,
     jdecide(Bool,Hyps, W ),
     !.
njdecide(and(Bool,_), Hyps, nand_il(W) ) :-
     !,
     njdecide(Bool,Hyps, W ),
     !.
njdecide(and(_,Bool), Hyps, nand_ir(W) ) :-
     !,
     njdecide(Bool,Hyps, W ),
     !.
/*
 * The following two clauses are required 
 * for Andrew Stevens datatype shell mechanism.
 * 
njdecide(Recog,_,unit ) :-
     Recog =.. [RName|Args],
     last(Arg,Args),
     functor(Arg,AF,_),
     tuple( shell_constructor, [CName, RName|_] ),
     AF \= CName,
     tuple( shell_constructor, [AF|_] ),
     !.

njdecide(Recog,Hyps, mutex(WitList) ) :-
     tuple( shell, [Type,_,_,_,_,_,Recogs] ),
     select(Recog, Recogs, RestRecogs ),
     !,
     \+ member( mutex(Type), Hyps ),
     jdecide_list( RestRecogs, [mutex(Type)|Hyps], WitList ).
 *
 */

njdecide_list( [H|T], Hyps, [HW|TW] ) :-
    njdecide( H, Hyps, HW ),
    njdecide_list( T, Hyps, TW ).
njdecide_list( [], _, [] ).

% next to ensure that  def of true is present
?- add_def({true}<==>int).





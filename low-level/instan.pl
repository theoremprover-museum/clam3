%*********
%*
%*  instantiated(+Term, +Sub, -InstdTerm ) -
%*  INstdTerm is Term instantiated through the application of the substitution
%*  Sub.
%*
%*       The code is complicated because of the need to deal with variable
%* capture.
%*
%********

:- lib_include( library(sets) ).

instantiated_list( [], _, [] ) :- !.

instantiated_list( L, Insts, InstdL ) :-
    findall( IE, (member(E,L), instantiated(E,Insts,IE)), InstdL ).

instantiated( Term, Insts, Instd ) :-
    findall( Free,
             ( member((_-Sub),Insts),
               freevarsinterm( Sub, Free )
             ),
             Frees ),
    !,
    union( Frees, SubFrees ),
    instantiated( Term, Insts, SubFrees, [], Instd ).

instantiated( Term, _, Term).

% If term is one which is to be instantiated
% replace it, as long as it is not a variable which is bound

instantiated( Term1, _, _, _, Term2 ) :-
    var(Term1),
    Term1=Term2,
    !.

instantiated( Term, Insts, _ , Bound, Instd ) :-
    member( (Term - Instd), Insts ),
    \+ member( Term, Bound ),
    !.




% The Subset type

instantiated( {Var:Type \ Pred}, Insts, SubFrees, Bound, {AVar:SType \ SPred} ) :-
    member( Var, SubFrees ),
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Pred, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SPred ).

instantiated( {Var:Type \ Pred}, Insts, SubFrees, Bound, {Var:SType \ SPred} ) :-
    !,
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    instantiated( Pred, Insts, SubFrees, [Var|Bound], SPred ),
    !.




%  The product type

instantiated( (Var:Type#Pred), Insts, SubFrees, Bound, (AVar:SType#SPred) ) :-
    member( Var, SubFrees ),
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Pred, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SPred ).

instantiated( (Var:Type#Pred), Insts, SubFrees, Bound, (Var:SType#SPred) ) :-
    !,
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    instantiated( Pred, Insts, SubFrees, [Var|Bound], SPred ),
    !.




% The function type

instantiated( (Var:Type=>Pred), Insts, SubFrees, Bound, (AVar:SType=>SPred) ) :-
    member( Var, SubFrees ),
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Pred, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SPred ).

instantiated( (Var:Type=>Pred), Insts, SubFrees, Bound, (Var:SType=>SPred) ) :-
    !,
    instantiated( Type, Insts, SubFrees, Bound, SType ),
    instantiated( Pred, Insts, SubFrees, [Var|Bound], SPred ),
    !.





% The lambda term

instantiated( lambda(Var,Pred), Insts, SubFrees, Bound, lambda(AVar,SPred) ) :-
    member( Var, SubFrees ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Pred, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SPred ).

instantiated( lambda(Var,Pred), Insts, SubFrees, Bound,lambda(Var,SPred) ) :-
    !,
    instantiated( Pred, Insts, SubFrees, [Var|Bound], SPred ).

% The bind body of induction and decision terms

instantiated( [Var,Pred], Insts, SubFrees, Bound, [AVar,SPred] ) :-
    member( Var, SubFrees ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Pred, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SPred ).

instantiated( [Var,Pred], Insts, SubFrees, Bound, [Var,SPred] ) :-
    !,
    instantiated( Pred, Insts, SubFrees, [Var|Bound], SPred ).


instantiated( [~|Binding], Insts, SubFrees, Bound, [~|SBinding] ) :-
    !,
    instantiated( Binding, Insts, SubFrees, Bound, SBinding ).

instantiated( [Var|Bind], Insts, SubFrees, Bound, [AVar,SBind] ) :-
    member( Var, SubFrees ),
    modify(Var, AVar),
    \+ member( AVar, SubFrees ),
    !,
    instantiated( Bind, [(Var-AVar)|Insts], [AVar|SubFrees], Bound, SBind ).

instantiated( [Var|Bind], Insts, SubFrees, Bound, [Var|SBind] ) :-
    !,
    instantiated( Bind, Insts, SubFrees, [Var|Bound], SBind ).





% If no binding required, and not something to be instantiated
% simply substitute it's arguments (if any).

instantiated( Term, _, _, _, Term ) :-
    (atom(Term);number(Term); (Term={A},atom(A)) ),
    !.

instantiated( Term, Insts, SubFrees, Bound, STerm ) :-
    Term =.. [Funct|Args],
    instantiateds(Args, Insts, SubFrees, Bound, SArgs ),
    STerm =.. [Funct|SArgs].

instantiateds( [H|T], Insts, SubFrees, Bound, [SH|ST] ) :-
    instantiated( H, Insts, SubFrees, Bound, SH ),
    instantiateds( T, Insts, SubFrees, Bound, ST ).
instantiateds( [], _, _, _, [] ).




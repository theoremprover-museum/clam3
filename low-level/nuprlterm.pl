%*******************
%*
%*   nuprlterm -  Module for converting terms expressed in a function
%*             programming style into equivalent Nuprl type-theory
%*             terms.
%*
%*******************

:- lib_include( library('strings.pl') ).

:- lib_include( nested_ops ).



%**************
%*
%*	curry_type( PreList, Type, CurriedType )
%*      - CurriedType is TYpe with the pre-condition in list form
%*      PreList attached as a curried pre-condition
%*
%*      exist_type( PreList, Type, ExistType )
%*      -  ExistType is Type with the pre-condition in list form
%*      PreList attached as a existential quantification
%*%*                     
%**************

curry_type( [(Var : Type)|RestPres], BareType, CurriedType ) :-
    CurriedType = ( Var : Type =>RestCurriedType),
    !,
    curry_type( RestPres, BareType, RestCurriedType ).

curry_type( [], A=>void, A => void ).
curry_type( H, C, A => B ) :-
    (var(H);var(C)),
    write( 'curry_type: non-dependent function type!' ),
    write( A => B ),
    nl,
    abort.

curry_type( [], BareType, BareType ).

exist_type( [(Var : Type)|RestPres], BareType, ExistType ) :-
    ExistType = ( Var : Type # RestExistType),
    !,
    exist_type( RestPres, BareType, RestExistType ).

exist_type( H, C, A # B ) :-
    (var(H);var(C)),
    write( 'exist_type: non-dependent product type!' ),
    write( A # B ),
    nl,
    abort.
exist_type( [], BareType, BareType ).



%*************
%*
%*	conjunct_type( +JudgList, -ConjGoal )
%*      - ConjGoal is the conjunctive goal equivalent to the
%*      list of goals in JudgList
%*
%*************

conjunct_type( [Type], Type ) :-
    !.
conjunct_type( [Type|RestTypes], ( Type # RestNestedOpForm ) ) :-
    conjunct_type( RestTypes, RestNestedOpForm ).

without_exists( (_:_#Rhs), Stripped ) :-
    !,
    without_exists( Rhs, Stripped ).
without_exists( T, T ).



%*********
%*
%*    curried_appl( +Funct, +Args, -CurriedApplication )
%*
%*    - Build the curried application of Funct to Args
%*
%*
%**********

curried_appl( Funct, [Hd|Tl], CurriedAppl ) :-
    curried_appl( (Funct of Hd), Tl, CurriedAppl ).

curried_appl( Funct, [], Funct ).
    
%*********
%*
%*    curried_lambda( +Funct, +Args, -CurriedApplication )
%*
%*    - Build the curried lambda abstraction of Body over Args
%*
%*
%**********

curried_lambdas( Body, [Hd|Tl], lambda(Hd,Curried) ) :-
    curried_lambdas( Body, Tl, Curried ).

curried_lambdas( Body, [], Body ).


%********
%*
%*
%*      new_var( Pre, NewVar )
%*
%*******

new_var( [Pre|Rest], [NewVar|RestNewVar], H ) :-
    new_var( Pre, NewVar ),
    \+ member( NewVar, H ),
    !,
    new_var( Rest, RestNewVar, [NewVar|H] ).
new_var( [], [], _ ).

new_var( Pre, Pre ).
new_var( Pre, NewVar ) :- 
    var(NewVar),
    !,
    genint(N),
    concat( Pre, N, NewVar ).

new_free_var( Pre, [V|R], H ) :-
    new_var( Pre, V ),
    free( [V], H ),
    !,
    new_free_var( Pre, R, [V:pnat|H] ).

new_free_var( _, [], _ ).



meta_term( Tm, Mtm ) :-
    freevarsinterm( Tm, Free ),
    length( Free, N ),
    length( Sub, N ),
    s( Tm, Sub, Free, Mtm ).


cdef_appl( DefName, [], DefName ) :- integer(DefName),!.
cdef_appl(DefName, [], {DefName} ) :- !.
cdef_appl( DefName, Args, Appl ) :- Appl =.. [DefName|Args],!,\+ (Args = []).

def_appl( DefName, [], {DefName} ) :- !.
def_appl( DefName, Args, Appl ) :- Appl =.. [DefName|Args],!,\+ (Args = []).


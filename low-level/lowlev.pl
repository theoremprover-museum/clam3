%*************
%*
%*   lowlev  -  A few useful low level predicates
%*
%*************

%select(A,S,R):-del(S,A,R).

rmember( E, [_|L] ) :-
    \+ L = [],
    rmember( E, L ).
rmember( E, [E|_] ).

filter( (V^P), [H|T], [H|R] ) :-
    \+ ( V=H,call( P )),
    !,
    filter( (V^P), T, R ).

filter( EP, [_|T], R ) :-
    filter( EP, T, R ).

filter( _, [], [] ).    


delete_first( [H|L],H,L ) :- !.
delete_first( [H|L], X, [H|D] ) :-
    delete_first( L,X, D ).
delete_first( [], _, [] ).


bak_abort :- true.
bak_abort :-
    nl,
    write( 'INTERNAL ERROR! SHould not have backtracked here!' ),
    nl,
    ((tactic_debug =: _, stopleap) ;abort),
    !.


stopleap.



   

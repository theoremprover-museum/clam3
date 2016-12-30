%***************
%*
%*	noise - Module for diagnostic output
%*
%**************

noise( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.
noise( _, Mesg ) :-
    write( Mesg ),
    flush_output(user_output),
    !.

noisenl( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.
noisenl( _, Mesg ) :-
    write( Mesg ),
    nl,
    !.

noisenl( L ) :-
    trace_plan(V,V),
    V < L,
    !.
noisenl( _ ) :-
    nl,
    !.
error( Mesg ) :-
    write( 'ERROR: ' ),
    write( Mesg ),
    nl,
    !.


noise_schema( L, _ ) :-
    trace_plan(V,V),
    V < L,
    !.

noise_schema( _, S) :- !,schema_list( S ).

schema_list( [ (H=>[Sb|RS]) | T ] ) :-
    write( '  ' ),
    write( H ),
    nl,
    write( ' => ' ),
    write( Sb ),
    nl,
    line_list( RS, 4),
    schema_list( T ).
schema_list( [] ).

noise_list( L, _ ) :-
    noise_level =: V,
    V < L,
    !.

noise_list( _, LL ) :-
    write( '[ ' ),
    line_list( LL, 2 ),
    write( ']' ).

line_list( [H|T], I ) :-
    tab(I),
    write( H ),
    nl,
    line_list(T, I ).
line_list( [], _ ).


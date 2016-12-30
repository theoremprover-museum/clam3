
%fix for the absolute path name problem
lib_fname( LibDir, Object, Kind, FN ) :-
           absolute_file_name(LibDir,LD),
           oldfilenames =: _,
           concat_atom( [LD, '/', Object, '.', Kind ], FN ).
lib_fname( LibDir, Object, Kind, FN ) :-
           absolute_file_name(LibDir,LD),
           concat_atom( [LD, '/', Kind, '/', Object ], FN ).

/*
lib_fname( LibDir, Object, Kind, FN ) :-
           oldfilenames =: _,
           concat_atom( [LibDir, '/', Object, '.', Kind ], FN ).
lib_fname( LibDir, Object, Kind, FN ) :-
           concat_atom( [LibDir, '/', Kind, '/', Object ], FN ).
*/

ttywrite(X) :- write(user,X).
ask(X) :- get0(X), in_eoln(X).
in_eoln(10) :- !.
in_eoln(_) :- get0(X),in_eoln(X).

:- op(900,      fy,     [not]).
:- op(700,      xfx,    [\=]) ; true.

T1 \= T2 :- \+ T1 = T2.
not Goal :- \+ Goal.
do_subcall :-
    read(X),
    !,
    call(X),
    !,
    fail.    

% **** ocunifiable/2 - Args are are unifiable with occurs check.
% **** Binding of Vars in X and Y unchanged.  

ocunifiable( X, Y ) :-
     \+ \+ ( numbervars(X,0,_),  X=Y ).

uniq_id( X ) :-
     recorded( '@id_ctr@',X, Ref ),
     SX is X + 1,
     erase(Ref),
     recorda( '@id_ctr@', SX, _ ),
     !.
uniq_id( 1 ) :-
     recorda( '@id_ctr@', 1, _ ).

% Construct banner, construct file name to save in, and save: 
save_it( N ) :- clam_version(V),name(V,Vname), 
   append(["CLaM Proof Planner Version ",Vname," (libraries only)"],Banner),
   dialect(D), 
   save_state(Banner, N).



:-       ensure_loaded(library(strings)),
	 ensure_loaded(library(directory)),
	 ensure_loaded(library(lists)),
         ensure_loaded(library(flatten)),
	 ensure_loaded(library(arg)),
	 ensure_loaded(library(occurs)),
	 ensure_loaded(library(findall)),
	 ensure_loaded(library(date)),
	 ensure_loaded(library(call)),
	 ensure_loaded(library(files)),
	 ensure_loaded(library(environ)),
	 ensure_loaded(library(sets)). % Already loaded by Oyster, but stated
                                       % here as well for completeness sake.


%***************
%*
%*	ttsub_terms -  Work out the subterms of nurprl term,
%*		  extended to allow unary sub terms.
%*
%*  ttsub_terms(+Tm,-Dterms) - Dterms are the subterms of Tm.
%*  ttsub_term(+Tm,?Dterm) - Dterm is a subterm of Tm.
%*
%***************

ttsub_terms( Tm, Dterms ) :-
    findall( Dterm, ttsub_term(Tm,Dterm), Dterms ),
    !.

ttsub_terms( _, [] ).


ttsub_term( V, _ ) :-
    var(V),
    !,
    fail.

ttsub_term( atom(A), atom(A) ) :-
    !.

ttsub_term( term_of(Name), term_of(Name) ) :-
    !.

ttsub_term( {Name}, {Name} ) :-
    atom(Name),
    !.

ttsub_term(Dterm,Dterm) :-
    atom(Dterm),
    !.

ttsub_term( T, T ).
ttsub_term( [H|T], Dterm ) :-
    append( _, [BTerm], [H|T] ),
    ttsub_term( BTerm, Dterm ).


ttsub_term( (_:T1#T2), Dterm ) :-		% *** Deal with binding types
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( (_:T1=>T2), Dterm ) :-
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( ({_:T1 \ T2}), Dterm ) :-
    ttsub_term(T1,Dterm );
    ttsub_term(T2,Dterm ).

ttsub_term( lambda(_,T), Dterm ) :-	% *** lambda term
    ttsub_term( T, Dterm ).


ttsub_term( Tm, Dterm ) :-		% *** Non-binding connectives etc
    Tm =.. [_|Args],
    member(Arg,Args),
    ttsub_term( Arg, Dterm ).



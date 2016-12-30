%*************
%*
%*   one_way -  One way matching of terms.
%*
%*   match_term( +Pattern, +Term, -Sub )
%*   - IF NO VARIABLES ARE BOUND IN Pattern, Sub is the substitution that
%*    needs to be applied to Pattern to make it match Term.
%*
%*************

match_term( Pattern, Term, Matching ) :-
    match_term( Pattern, Term, [], [], Matching ).

match_term( Pattern, Term, _, SoFar, SoFar ) :-
    var(Pattern),
    !,
    Pattern = Term.
% **** Variable matches anything

match_term( Pattern, Term, Bind, SoFar, SoFar ) :-
    ttvar(Pattern),
    (
      member( (Pattern - OldMat), Bind ) ;
      member( (Pattern - OldMat), SoFar )
    ),
    !,
    OldMat = Term.

match_term( Pattern,Term, _, SoFar, [ (Pattern - Term )| SoFar ] ) :-
    ttvar(Pattern),
    !.


% **** Atom matches only the same atom.

match_term( atom(PTerm), atom(PTerm), _, SoFar, SoFar ) :-
    !,
    atom(PTerm).

match_term( term_of(Name), term_of(Name), _, SoFar, SoFar ) :-
    !.
match_term( {PTerm}, {PTerm}, _, SoFar, SoFar ) :-
    atom(PTerm).



% **** The various kinds of binding term
% **** #, ->, { | }, lambda, [ v1,...,vn,t]

match_term( {PVar:PBType \ PPred}, {TVar:TBType\TPred}, Bind, SoFar, Match ) :-
    !,
    match_term( PBType, TBType, Bind, SoFar, NewSoFar ),
    match_term( PPred, TPred, [(PVar-TVar)|Bind], NewSoFar, Match ).


match_term( (PVar:PBType->PPred), (TVar:TBType->TPred), Bind, SoFar, Match ) :-
    !,
    match_term( PBType, TBType, Bind, SoFar, NewSoFar ),
    match_term( PPred, TPred, [(PVar-TVar)|Bind], NewSoFar, Match ).


match_term( (PVar:PBType#PPred), (TVar:TBType#TPred), Bind, SoFar, Match ) :-
    !,
    match_term( PBType, TBType, Bind, SoFar, NewSoFar ),
    match_term( PPred, TPred, [(PVar-TVar)|Bind], NewSoFar, Match ).


match_term( lambda(PVar,PPred), lambda(TVar, TPred), Bind, SoFar, Match ) :-
    !,
    match_term( PPred, TPred, [(PVar-TVar)|Bind], SoFar, Match ).


match_term( BindPat, BindTerm, Bind, SoFar, Match ) :-
    append( PatVars, [ PatTerm ], BindPat ),
    append( TermVars, [ TermTerm ], BindTerm ),
    !,
    zip( VarBind, PatVars, TermVars ),
    append( VarBind, Bind, NewBind ),
    match_term( PatTerm, TermTerm, NewBind, SoFar, Match ).


% **** A non-binding term matches if it's functor matches
% **** and it's arguments match.

match_term( Pattern,Term, Bind, SoFar, Match ) :-
    Pattern =.. [Funct | PArgs],
    Term =.. [Funct | TArgs],
    match_term_list( PArgs, TArgs, Bind, SoFar, Match ).


% **** Match (argument) lists of term in pattern and term

match_term_list( [HdPatts|TlPatts], [HdTerms|TlTerms], Bind, SoFar, Match ) :-
    match_term( HdPatts, HdTerms, Bind, SoFar, NextSoFar ),
    match_term_list( TlPatts, TlTerms, Bind, NextSoFar, Match ).

match_term_list( [], [], _, SoFar, SoFar ).





%
% casesplit_set_implicit/2
%
%
casesplit_set_implicit(Pat, Context, Cases):-
    \+ atomic(Pat),
    freevarsinterm(Pat, Vars),
    member(Var, Vars),
    member(Var:Typ, Context),
    check_coverage(Pat, Var, Typ),
    type_to_casesplit(Var:Typ, Cases),!.

check_coverage(Pat, Var, Typ):-
    canonical_constructors(Typ, CList),
    forall{C\CList}:(replace_all(Var, C, Pat, NewPat),
                     func_defeqn(NewPat, _)).

canonical_constructors(pnat, [0,s(_)]).
canonical_constructors(pnat list, [nil,_::_]).

type_to_casesplit(Var:pnat, [[Var = 0 in pnat],
                             [Var = 0 in pnat => void,
                              Var = s(pred(Var)) in pnat]]).
type_to_casesplit(Var:pnat list, [[Var = nil in pnat list],
                                  [Var = hd(Var)::tl(Var) in pnat list,
                                   Var = nil in pnat list => void]]).


    
    
    
    
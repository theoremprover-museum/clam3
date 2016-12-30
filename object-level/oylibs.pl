% The Oyster system was developed using the Quintus Prolog system. This
% file implements/simulates some of the Quintus dependent features, and
% allows Oyster to run on any Prolog system with Edinburgh syntax,
% as originally defined for the DEC-10 implementation of Prolog by David
% Warren, as described in
% "Implementing Prolog - Compiling Predicate Logic Programs",
% Research Reports 39 & 40, Department of Artificial Intelligence,
% University of Edinburgh, 1977.
%
% This file should be loaded >*before*< any of the other source code of
% the Oyster system is loaed.

?- if( \+ dialect(qui) ).

:- op(900, fx, [(dynamic)]).
:- op(1150,fx, [(multifile)]).

dynamic _.
multifile _.

%   concat_atom(+ListOfTextObjects, -Combined)
%   concatenates the names of all the text objects in the list
%   and returns an atom whose name is the combined characters.
%   Valid text objects are either character lists, atoms or numbers.
concat_atom(List,Atom) :- concat_atom1(List, ListTmp), name(Atom,ListTmp).
% concat_atom1([],'').
concat_atom1([],[]).
concat_atom1([H|T], Out) :-
    atomic(H), !, name(H,HH), concat_atom1(T,TT), append(HH,TT,Out).
concat_atom1([H|T], Out) :-
    H =.. [.|_], concat_atom1(T,TT), append(H,TT, Out).

append([],X,X).
append([H|T],X,[H|L]):-append(T,X,L).

member(H,[H|_]).
member(H,[_|L]):-member(H,L).
 
?- if( \+ dialect( sic ) ).

atom_chars(Atom,Chars) :- atom(Atom), !, name(Atom,Chars).
atom_chars(Atom,Chars) :- var(Atom), \+ var(Chars), name(Atom,Chars).

?- endif.

% The following are copied from the Quintus library.
% All are trivial, nevertheless:
% Copyright (C) 1987, Quintus Computer Systems, Inc.  All rights reserved.
%	union/3
%	union/2
%	union1/2
%	union2/2
%	memberch/2
%	subtract/3
%	is_set/1
%	nonmember/2
%	del_element/3
%	remove_dups/2
%	correspond/4

%   union(+Set1, +Set2, ?Union)
%   is true when subtract(Set1,Set2,Diff) and append(Diff,Set2,Union),
%   that is, when Union is the elements of Set1 that do not occur in
%   Set2, followed by all the elements of Set2.
union([], Union, Union).
union([Element|Elements], Set, Union) :-
	memberchk(Element, Set), !,
	union(Elements, Set, Union).
union([Element|Elements], Set, [Element|Union]) :-
	union(Elements, Set, Union).

%   union(+ListOfSets, ?Union)
%   is true when Union is the union of all the sets in ListOfSets.
%   It has been arranged with storage turnover in mind.
union(Sets, Union) :-
	union1(Sets, Answer),
	append(Answer, [], Answer),	% cauterise it
	!,
	Union = Answer.

union1([], _).
union1([Set|Sets], Answer) :-
	union2(Set, Answer),
	union1(Sets, Answer).

union2([], _).
union2([Element|Elements], Answer) :-
	memberchk(Element, Answer),	% add_element hack
	union2(Elements, Answer).

%   memberchk(+Element, +Set)
%   means the same thing as member/2, but may only be used to test whether a 
%   known Element occurs in a known Set.  In return for this limited use, it
%   is more efficient than member/2 when it is applicable.
memberchk(Element, [Element|_]) :- !.
memberchk(Element, [_|Rest]) :-
	memberchk(Element, Rest).

%   subtract(+Set1, +Set2, ?Difference)
%   is like intersect, but this time it is the elements of Set1 which
%   *are* in Set2 that are deleted.
subtract([], _, []).
subtract([Element|Residue], Set, Difference) :-
        memberchk(Element, Set), !,
        subtract(Residue, Set, Difference).
subtract([Element|Residue], Set, [Element|Difference]) :-
        subtract(Residue, Set, Difference).

%   is_set(+List)
%   is true when List is a proper list that contains no repeated elements.
%   That, is, List represents a set in the style used by this package.
%   See the description of nonmember/2 for some restrictions.
is_set([Head|Tail]) :- !,
        nonmember(Head, Tail),
        is_set(Tail).
is_set([]).

%   nonmember(+Element, +Set)
%   means that Element does not occur in Set.  It does not make sense
%   to instantiate Element in any way, as there are infinitely many
%   terms which do not occur in any given set.  Nor can we generate
%   Set; there are infinitely many sets not containing a given Element.
%   Read it as "the given Element does not occur in the given list Set".
%   This code was suggested by Bruce Hakami; seven versions of this
%   operation were benchmarked and this found to be the fastest.
%   The old code was for DEC-10 Prolog, which did not compile (\+)/1.
nonmember(Element, Set) :-
        \+ member(Element, Set).

%   del_element(Elem, Set1, Set2)
%   is true when Set1 and Set2 are sets represented as unordered lists,
%   and Set2 = Set1 \ {Elem}.  It may only be used to calculate Set2
%   given Elem and Set1.  If Set1 does not contain Elem, Set2 and Set1
%   will be equal.  I wanted to call this predicate 'delete', but other
%   Prologs have used that for 'select'.  If Set1 is not an unordered
%   set, but contains more than one copy of Elem, only the first will
%   be removed.  See delete/3 for a predicate which will delete all the
%   copies of a given element.

del_element(Elem, [Elem|Set2], Set2) :- !.
del_element(Elem, [X|Set1], [X|Set2]) :- !,
	del_element(Elem, Set1, Set2).
del_element(_, [], []).

%   remove_dups(List, Pruned)
%   removes duplicated elements from List, which should be a proper list.
%   If List has non-ground elements, Pruned may contain elements which
%   unify; two elements will remain separate iff there is a substitution
%   which makes them different.  E.g. [X,X] -> [X] but [X,Y] -> [X,Y].

remove_dups(List, Pruned) :-
	sort(List, Pruned).

%   correspond(X, Xlist, Ylist, Y)
%   is true when Xlist and Ylist are lists, X is an element of Xlist, Y is
%   an element of Ylist, and X and Y are in similar places in their lists.
%   For a similar predicate without the cut, see select/4 below.

correspond(X, [X|_], [Y|_], Y) :- !.
correspond(X, [_|T], [_|U], Y) :-
	correspond(X, T, U, Y).

?- endif.

?- if( dialect(qui) ).

:- ensure_loaded(library(basics)).
:- ensure_loaded(library(sets)).
:- ensure_loaded(library(lists)).

?- endif.

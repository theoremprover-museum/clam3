/* This file contains some patches to make SWI Prolog look more like
 * Quintus/NIP.
 * The size of this file is a tribute to the DEC10 compatibility of SWI
 * Prolog!
 *
 * This file assumes that the file nip.pl has already been loaded.
 *
 * At the end of the file are some patches/workarounds for bugs in SWI
 * Prolog. 
 */

/* The following line should be declared before loading Oyster!! */


/* :- assert((:-(Goal):-call(Goal))). */

lib_fname( LibDir, Object, Kind, FN ) :-
          concat_atom( [LibDir, '/', Kind, '/', Object ], FN ).
	   

/* ************* UTIL PREDICATES ******************* */

ttywrite(X) :- write(user,X).
ttynl :- nl(user).
ask(X) :- get0(X), in_eoln(X).
in_eoln(10) :- !.
in_eoln(_) :- get0(X),in_eoln(X).

uniq_id( X ) :- gensym('',X).

constant(T):-
    constant(T, _).

nth0i(0, [Head|_], Head) :- !.
nth0i(N, [_|Tail], Element) :-
        M is N - 1,
        nth0i(M, Tail, Element).

%   nth0(?N, +List, ?Element, ?Rest)
%   nth0/4 unifies Element with the nth element in List, counting the
%   first element as 0 and Rest with rest of the elements.

nth0(N, List, Element, Rest) :-
        integer(N), !,
        N >= 0,
        nth0i(N, List, Element, Rest).
nth0(N, List, Element, Rest) :-
        var(N),
        nth0v(List, Element, 0, N, Rest).

nth0v([Element|Tail], Element, Index, Index, Tail).
nth0v([Head|Tail], Element, M, Index, [Head|Rest]) :-
        N is M + 1,
        nth0v(Tail, Element, N, Index, Rest).

nth0i(0, [Head|Tail], Head, Tail) :- !.
nth0i(N, [Head|Tail], Element, [Head|Rest]) :-
        M is N - 1,
        nth0i(M, Tail, Element, Rest).

nth1(N,[H|T],Elem) :- nth0(N1,[H|T],Elem), N is N1+1.
nth1(N,[H|T],Elem,Rest) :- nth0(N1,[H|T],Elem,Rest), N is N1+1.

	% must_be_integer(Int,ArgNr,Call)
	% Succeeds iff Int is integer, where Int appears as the ArgNr-th
	% argument to Call. Protests if Int not integer.
	% Simulates predicate from Quintus library types
must_be_integer(Int,_,_) :- integer(Int),!.
must_be_integer(Int,ArgNr,Call) :-
    functor(Call,F,N), nl,
    writef('! Type failure in argument %t of %t\n',[ArgNr,F/N]),
    writef('! integer expected, but found %t\n',[Int]),
    writef('! Goal: %t\n',[Call]),
    !,fail.


%   contains_term(+Kernel, +Expression)
%   is true when the given Kernel occurs somewhere in the Expression.
%   It can only be used as a test; to generate sub-terms use sub_term/2.

contains_term(Kernel, Expression) :-
        \+ free_of_term(Kernel, Expression).

%   free_of_term(+Kernel, +Expression)
%   is true when the given Kernel does not occur anywhere in the
%   Expression.  NB: if the Expression contains an unbound variable,
%   this must fail, as the Kernel might occur there.  Since there are
%   infinitely many Kernels not contained in any Expression, and also
%   infinitely many Expressions not containing any Kernel, it doesn't
%   make sense to use this except as a test.

free_of_term(Kernel, Kernel) :- !,
        fail.
free_of_term(Kernel, Expression) :-
        atomic(Expression),!.
free_of_term(Kernel, Expression) :-
        functor(Expression, _, Arity),          %  can't be a variable!
        free_of_term(Arity, Expression, Kernel).

free_of_term(0, _, _) :- !.
free_of_term(N, Expression, Kernel) :-
        arg(N, Expression, Argument),
        free_of_term(Kernel, Argument),
        M is N-1,
        free_of_term(M, Expression, Kernel).

%   sub_term(?Kernel, +Term)
%   is true when Kernel is a sub-term of Term.  It enumerates the
%   sub-terms of Term in an arbitrary order.  Well, it is defined
%   that a sub-term of Term will be enumerated before its own
%   sub-terms are (but of course some of those sub-terms might be
%   elsewhere in Term as well).

sub_term(Term, Term).
sub_term(SubTerm, Term) :-
        nonvar(Term),
        functor(Term, _, N),
        sub_term(N, Term, SubTerm).

sub_term(N, Term, SubTerm) :-
        arg(N, Term, Arg),
        sub_term(SubTerm, Arg).
sub_term(N, Term, SubTerm) :-
        N > 1,
        M is N-1,
        sub_term(M, Term, SubTerm).

%   ocunifiable/2 - Args are are unifiable with occurs check.
%   Binding of Vars in X and Y unchanged.
% This is nothing of the kind in fact, just 1-way matching
% but is sufficient for the purpose to which it is put in
% clam.

ocunifiable( X, Y ) :-
     \+ \+ ( numbervars(X,'junk',0,_),  X=Y ;
             numbervars(Y,'junk',0,_),  X=Y 
	   ).


%   append(+ListOfLists, ?List)
%   is true when ListOfLists is a list [L1,...,Ln] of lists, List is
%   a list, and appending L1, ..., Ln together yields List.  The
%   ListOfLists **must** be a proper list.  (Strictly speaking we
%   should produce an error message if it is not, but this version
%   fails.)  Additionally, either List should be a proper list, or
%   each of L1, ..., Ln should be a proper list.  The behaviour on
%   non-lists is undefined.  ListOfLists must be proper because for
%   any given solution, infinitely many more can be obtained by
%   inserted nils ([]) into ListOfList.

append(-, _) :- !, fail.        % reject partial lists.
append([], []).
append([L|Ls], List0) :-
        append(L, List1, List0),
        append(Ls, List1).



selectchk(X, [X|R],     Residue) :- !, Residue = R.
selectchk(X, [A,X|R],   Residue) :- !, Residue = [A|R].
selectchk(X, [A,B,X|R], Residue) :- !, Residue = [A,B|R].
selectchk(X, [A,B,C|L], [A,B,C|R]) :-
	selectchk(X, L, R).

select(X, [X|R],     R        ).
select(X, [A,X|R],   [A|R]    ).
select(X, [A,B,X|R], [A,B|R]  ).
select(X, [A,B,C|L], [A,B,C|R]) :-
	select(X, L, R).

remove_dups( [H|T], R ) :-
	remove_dups( T, RR ),
	( member( H, RR ) -> R = RR ; R = [H|RR] ),
	!.
remove_dups( [], [] ).

intersect(Set1, Set2) :-
	member(Element, Set1),		%  generates Elements from Set1
	memberchk(Element, Set2),	%  tests them against Set2
	!.				%  if it succeeds once, is enough.

union( [H|T], R ) :-
	union( T, RR ),
	union( H, RR, R ).
union( [], [] ).

perm( A,B ) :- msort(A,C), msort(B,C).
seteq( A, B ) :- sort(A,C), sort(B,C).

intersection([Set|Sets], Intersection) :-
	intersection1(Set, Sets, Intersection).

intersection1([], _, []).
intersection1([Element|Elements], Sets, Intersection) :-
	memberchk_all(Sets, Element),
	!,
	Intersection = [Element|Rest],
	intersection1(Elements, Sets, Rest).
intersection1([_|Elements], Sets, Intersection) :-
	intersection1(Elements, Sets, Intersection).

memberchk_all([], _).
memberchk_all([Set|Sets], Element) :-
	memberchk(Element, Set),
	memberchk_all(Sets, Element).

%   subseq(Sequence, SubSequence, Complement)
%   is true when SubSequence and Complement are both subsequences of the
%   list Sequence (the order of corresponding elements being preserved)
%   and every element of Sequence which is not in SubSequence is in the
%   Complement and vice versa.  That is,
%   length(Sequence) = length(SubSequence)+length(Complement), e.g.
%   subseq([1,2,3,4], [1,3,4], [2]).  This was written to generate subsets
%   and their complements together, but can also be used to interleave two
%   lists in all possible ways.  Note that if S1 is a subset of S2, it will
%   be generated *before S2 as a SubSequence and *after it as a Complement.

subseq([], [], []).
subseq([Head|Tail], Sbsq, [Head|Cmpl]) :-
	subseq(Tail, Sbsq, Cmpl).
subseq([Head|Tail], [Head|Sbsq], Cmpl) :-
	subseq(Tail, Sbsq, Cmpl).

%   same_length(?List1, ?List2)
%   is true when List1 and List2 have the same number of elements.

same_length([], []).
same_length([_|L1], [_|L2]) :-
        same_length(L1, L2).

%   same_length(?List1, ?List2, ?Length)
%   is true when List1 and List2 are both lists, Length is a non-negative
%   integer, and both List1 and List2 have exactly Length elements.  No
%   relation between the elements of the lists is implied.  If Length
%   is instantiated, or if either List1 or List2 is bound to a proper
%   list, same_length is determinate and terminating.  library(length)
%   has more predicates with this structure.

same_length(List1, List2, Length) :-
	(   integer(Length) ->
	    Length >= 0,
	    'same length'(Length, List1, List2)
	;   nonvar(Length) ->
	    must_be_integer(Length, 3, same_length(List1,List2,Length))
	;   var(List1) ->		% swap List1 and List2 around to
	    'same length'(List2, List1, 0, Length)
	;
	    'same length'(List1, List2, 0, Length)
	).

'same length'(0, List1, List2) :- !,	% delay unification
	List1 = [],			% to block infinite loops
	List2 = [].
'same length'(N, [_|Rest1], [_|Rest2]) :-
	M is N-1,			% N > 0, M >= 0
	'same length'(M, Rest1, Rest2).


'same length'([], [], N, N).
'same length'([_|Rest1], [_|Rest2], I, N) :-
	J is I+1,
	'same length'(Rest1, Rest2, J, N).


%   genarg(?N, +Term, ?Arg)
%   is true when arg(N, Term, Arg) is true, except that it can solve
%   for N.  Term, however, must be instantiated.

genarg(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        arg(N, Term, Arg).
genarg(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg(Arity, Term, Arg, N).

genarg(1, Term, Arg, 1) :- !,
	arg(1, Term, Arg).
genarg(N, Term, Arg, N) :-
	arg(N, Term, Arg).
genarg(K, Term, Arg, N) :-
	K > 1, J is K-1,
	genarg(J, Term, Arg, N).

%   genarg0(?N, +Term, ?Arg)
%   succeeds when N > 0 and arg(N, Term, Arg) is true
%   or when N =:= 0 and functor(Term, Arg, _) is true.
genarg0(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        (   N =:= 0 -> functor(Term, Arg, _)
        ;   arg(N, Term, Arg)
        ).
genarg0(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg0(Arity, Term, Arg, N).
genarg0(N, Term, Arg) :-
        integer(N),
        nonvar(Term),
        !,
        (   N =:= 0 -> functor(Term, Arg, _)
        ;   arg(N, Term, Arg)
        ).
genarg0(N, Term, Arg) :-
        var(N),
        nonvar(Term),
        !,
        functor(Term, _, Arity),
        genarg0(Arity, Term, Arg, N).

genarg0(0, Term, Arg, 0) :- !,
	functor(Term, Arg, _).
genarg0(N, Term, Arg, N) :-
	arg(N, Term, Arg).
genarg0(K, Term, Arg, N) :-
	K > 0, J is K-1,
	genarg0(J, Term, Arg, N).


/* ******************* ENVIRONMENT *************** */

reconsult(F) :- consult(F).

compile(F) :- consult(F).

file_exists(F) :- exists_file(F).

environ(Var,Val) :- getenv(Var,Val).

numbervars(Term,Begin,End) :- numbervars(Term,'$VAR',Begin,End).

datime(date(Year,Month1,Day,Hour,Min,Sec)) :-
    get_time(T),
    convert_time( T, Year, Month, Day, Hour, Min, Sec,_),
    % Emulate Quintus bug....:
    Month1 is Month-1.

save(File) :- save_program(File, [goal = version]).

version :- '$welcome', recorded(version,Text,_),write(Text),nl,fail.
version.
version(Text) :- recordz(version,Text,_).



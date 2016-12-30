%  This file contains a collection of predicates that are generally useful
%  in the context of any Prolog program.                                

  bye :- nl,halt.

  ascii(Code,Char) :- name(Char,[Code]).

%  append([],X,X).
%  append([U|L],X,[U|M]) :- append(L,X,M).

  lp_reverse(L1,L2) :- rev1(L1,L2,[]).
  rev1([],L,L) :- !.
  rev1([X|L],L1,L2) :- rev1(L,L1,[X|L2]), !.

  append_names(Name1,Name2,Name) :-
	name(Name1,Ascii1), name(Name2,Ascii2), 
	append(Ascii1,Ascii2,Ascii), name(Name,Ascii), !.

% Checking if an object is in a list. Succeeds only once if at all.
  lp_member(X,[X|L]) :- !.
  lp_member(X,[Y|L]) :- lp_member(X,L).

% Checking if an object is in a list. May succeed several times.
  memb(X,[X|L]).
  memb(X,[Y|L]) :- memb(X,L).

  belongs_to(X,L) :- memb(X,L).

% Same as lp_member, only does not instantiate variables to make objects equal.
  memb_inst(X,[Y|L]) :- X == Y, !.
  memb_inst(X, [Y|L]) :- lp_member(X,L).

%  nth(N,L,X) if X is the Nth element in L
%  nth(N,L,X) :- nth(N,L,X,1).
%  nth(N,[X|L],X,N).
%  nth(N,[Y|L],X,M) :- M1 is M+1, nth(N,L,X,M1).

% lp_reverse_cdr(L1,L2) is true if L2 is L1 with the last element lp_removed
lp_reverse_cdr([_],[]).
lp_reverse_cdr([X|L],[X|K]) :- !, lp_reverse_cdr(L,K).

% Set union; when represented by lists, union involves removing duplicates.
join([],K,K).
join([X|L],K,M) :- lp_member(X,K), !, join(L,K,M).
join([X|L],K,[X|M]) :- join(L,K,M).


join_at_end(List1,[],List1) :- !.
join_at_end(List1,[X|List2],List4) :-
	join_el_at_end(List1,X,List3), join_at_end(List3,List2,List4), !.

join_el_at_end([],El,[El]) :- !.
join_el_at_end([El|List],El,[El|List]) :- !.
join_el_at_end([X|List1],El,[X|List2]) :- 
			join_el_at_end(List1,El,List2), !.



% Removing an occurrence of an item from a list
  lp_remove(X,[],[]).
  lp_remove(X,[X|L],L).
  lp_remove(X,[Y|L],[Y|L1]) :- lp_remove(X,L,L1).

% Removing the first occurrence - if it exists - of an element from a list
  lp_remove_first(X,[],[]) :- !.
  lp_remove_first(X,[X|L],L) :- !.
  lp_remove_first(X,[Y|L],[Y|L1]) :- lp_remove_first(X,L,L1), !.

% Removing the first occurrence of an item from a list. Fails if the 
% item is not in the list
  lp_remove_lp_member(X,[X|L],L) :-  !.
  lp_remove_lp_member(X,[Y|L],[Y|L1]) :- lp_remove_lp_member(X,L,L1).

% Removing an element from a set - there may be multiple occurrences
  lp_remove_elt(X,[],[]) :- !.
  lp_remove_elt(X,[X|L],K) :-  lp_remove_elt(X,L,K), !.
  lp_remove_elt(X,[Y|L],[Y|K]) :- lp_remove_elt(X,L,K), !.

% delete_list(L1,L2,L3) is true if L2 - L1 = L3.
  delete_list([],L2,L2).
  delete_list([X|L],L2,L3) :- lp_remove_elt(X,L2,L0), delete_list(L,L0,L3).

% Removing the first N elements from a list
  remainder(L,0,L) :- !.
  remainder([X|L1],N,L2) :- N1 is N-1, remainder(L1,N1,L2), !.


% Checking if one list results from permuting the elements of the other
   lp_permutation([],[]).
   lp_permutation([X|L],K) :- !, lp_remove_lp_member(X,K,K1), lp_permutation(L,K1).


% This routine is an adaptation of the one in Clocksin & Mellish. It may be 
%  argued that only the commented out version is correct, but the one used
%  works in C-Prolog, and is perhaps faster!

  lp_gensym(Root, Atom) :- get_num(Root,Num), append_names(Root,Num,Atom), !.

  :- dynamic current_num/2.

  get_num(Root,Num) :-  retract(current_num(Root,Num1)),!, Num is Num1+1,
			asserta(current_num(Root,Num)).
  get_num(Root,1)   :-  asserta(current_num(Root,1)).


%  lp_gensym(Root, Atom) :- get_num(Root,Num), name(Root,Name1),
%		integer_name(Num,Name2), append(Name1,Name2,Name),
%		name(Atom,Name).
% get_num(Root,Num) :-  retract(current_num(Root,Num1)),!, Num is Num1+1,
%		asserta(current_num(Root,Num)).
% get_num(Root,1)   :-  asserta(current_num(Root,1)).
%  integer_name(Int,List) :- integer_name(Int,[],List).
% integer_name(I,Sofar,[C|Sofar]) :- I<10,!,C is I+48.
% integer_name(I,Sofar,List) :-  Bothalf is I mod 10,
%			 Tophalf is I // 10, 
%			 C is Bothalf+48, 
%			 integer_name(Tophalf,[C|Sofar],List).


%  count_up(N,L,M) if L is a list of integers from N to M, inclusive. 
  count_up(N,[],M) :-  N>M, !.
  count_up(N,[N],N) :- !.
  count_up(N,[N|L],M) :- !, N1 is N+1, count_up(N1,L,M).


% This is needed for versions before 2.0
%retractall(X) :- retract(X), fail.
%retractall(X) :- retract((X :- Y)), fail.
%retractall(X).

%  This has to be defined correctly if library(files) is unavailable
%  file_exists(File) :- exists(File).


% Write out the list of text, one entry per line.

   write_text([]).
   write_text([Text|Rest]) :- write(Text), nl, write_text(Rest).


% Write out n blank lines.

   blanklines(0) :- !.
   blanklines(N) :- N > 0, nl, N1 is (N - 1), blanklines(N1).


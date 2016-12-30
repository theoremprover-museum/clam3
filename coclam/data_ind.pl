/************************************************************************

      File: data_ind.pl
      Author: Louise Dennis
      Last Modified: 19th August 1997

      static semantics, and transition rules for a functional
      programming language in which tree, list and integer types are all lazy.

************************************************************************/
subtype_lang(pnat, int).

%%%  Ugly extras for type checking of named variables.
data(V, T, [V:T], blip):- \+var(V), atomic(V), var(T), !.
data(V, T, [V:T], blip):- \+var(V), atomic(V), data(_, Ty, _, _), Ty == T, !.
data(V, T, [V:T], blip):- \+var(T), var(V), !.

%%%  pnat implies integer
data(A, T, B, C):- T==int, data(A, pnat, B, C).

%%  pnat statics
data(0, pnat, [], non_rec).
data(s(N), pnat, [N:pnat], rec).

%% stream statics
data(nil, C list, [], non_rec).
data(H::T, C list, [H:C, T:C list], rec).

%% binary tree statics.
data(leaf(V), bintree(T), [V:T], non_rec).
data(node(L, Lt, R), bintree(T), [L:T, Lt:bintree(T), R:bintree(T)], rec).

%% infinite tree statics
data(node(L, R), tree(T), [L:T, R:list(tree(T))], rec).

%% boolean statics
data(true, bool, [], non_rec).
data(void, bool, [], non_rec).

%% Function statics
data(F, A=>B, [], blip):- atomic(F), ground([A, B]), \+ B = void.
data(F, A=>B, [], blip):-
	\+ var(F),
	F =.. [Functor|_],
        recorded(theorem, theorem(Functor, eqn, Rule, _), _),
	precon_matrix(Vars, []=>L=_ in B, Rule),
	member(_:A, Vars), !.

%% statement of active and coinductive types.
active([pnat, C list, bintree(T), tree(T)]).
coinductive([pnat, C list, bintree(T), tree(T)]).

%% transition rules - not including the reduction rule which is
%% emobidied in the intro1 method.
%%
%% integers
transition([N:pnat], N, num(N), bot).
transition([N:int], N, num(N), bot).
transition([N:pnat], type(N, pnat), num(N), bot).

%% streams
transition([], nil, nil, bot).
transition([], type(nil, list(T)), nil, type(bot, bot)).
transition([], H::T, hd, H).
transition([], H::T, tl, T).
transition([], type(H::T, list(Type)), hd, type(H, Type)).
transition([], type(H::T, list(Type)), tl, type(T, list(Type))).


%% binary trees
transition([], leaf(V), label, V).
transition([], node(L, Lt, R), label, L).
transition([], node(L, Lt, R), left, Lt).
transition([], node(L, Lt, R), right, R).
transition([], type(leaf(V), bintree(Type)), label, type(V, Type)).
transition([], type(node(L, Lt, R), bintree(Type)), label, type(L, Type)).
transition([], type(node(L, Lt, R), bintree(Type)), left, type(Lt, bintree(Type))).
transition([], type(node(L, Lt, R), bintree(Type)), right, type(R, bintree(Type))).


%% infinite trees
transition([], node(L, T), trees, T).
transition([], node(L, T), label, L).
transition([], type(node(L, T), tree(Type)), trees, type(T, list(trees(Type)))).
transition([], type(node(L, T), tree(Type)), label, type(L, Type)).

%% booleans
transition([V:bool], V, bool(V), bot).


data:-consult('~/xclam/data_ind.pl').



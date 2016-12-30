/*****************************************************************************\

%% File: gen_critic.pl

%% Author: Louise Dennis

%% Updated: 3rd July 1997

\*****************************************************************************/

%% 4th September, modification made because of confusions arising out
%% of variable subsitutions.  order_subs added.  Cal to repl in
%% gen_critic modified to exclude Vs, final call to set_to_function
%% from gen_critic also modified.

 %% gen_critic(+SetofFunctionRanges, -SetofFunctionRanges)
 %% Examines the function ranges to see if any subset of them have a
 %% common generalisation of the form discussed in BBNote 1107, and in
 %% Toby Walsh Generalisation Critic Paper and if so includes that
 %% generalisation.
 %%
 %% A Note on terminology.
 %%
 %% I'm looking for a sequence of terms S0, S1, ....
 %% the ith term in the sequence is Si, the next term (s(i)th term) is Ssi.
 %%
 %% I want Si = G(Ui) and Ssi = G(H(Ui)).
 %%
 %% Lterms is a list of terms of the form range(%x. term).
 %% LamTerm indicates a term of the form %x. term
 %% Term indicates a term without lambda abstractions.
gen_critic(Seq, [range(TypB-LamGT, Con0)|RLterms]):-
	reverse(Seq, [range(TypB-LamS0, Con0)|Lterms]),
	set_to_function(Vs, LamS0, S0),
        sub_set(Lterms, [], Sequence, RLterms),
	Sequence \== [],
	%% Need at least two elements in the Sequence to form a generalisation.
	seqlist(LamS0, Sequence, G-P, LamH, UPos, S1),
	%% Finds G, H and the position(s) within the term of U - the
	%% Ui are all different)
	findu(S1, U0, UPos),
	%% findu are the U0 + position
	%% Finds U0
	dm(S0, S1, _, SubsS1S0),
        variable_subs(Vs, SubsS1S0, SubsS1S0varonly),
	order_subs(SubsS1S0varonly, SubsOrd),
	repl(U0, U0d, SubsOrd),
	ghnu0(G-P, LamH, U0d, Nat:pnat),
	rem_brackets(G, BRLessG),
	%% Forms the term G(H^n(U0)) - the generalisation.
%%	set_to_function([Nat:pnat|Vsd], LamGT, BRLessG),
	set_to_function([Nat:pnat|Vs], LamGT, BRLessG),
	make_ground(LamGT).
gen_critic(Lterms, Lterms).     %p% If no generalisation can be found

 %% seqlist(+LamTerm, +Sequence, ?G, ?H, ?Upositions)
 %% Checks to see if Sequence is a list of terms with the same G, H,
 %% and Upositions.
seqlist(_, [], _, _, _, _).
seqlist(LamSi, [range(_-LamSsi, Coni)|Rest], G, LamH, UPoslist, Ssi):-
	set_to_function(Vi, LamSi, Si),
	set_to_function(_, LamSsi, Ssi),
	       %% Pick a candidate next member of sequence
	dm(Si, Ssi, AnnTerm, SubsSsiSi),
	wave_fronts(Si, WFlist, AnnTerm),
	       %% perform difference matching and find positions of
	       %% wave fronts and holes
	findhu(Si, WFlist, HU, Ui),
	\+ member(appn(0, _, _)-_, HU),
	       %% HU list of h(u) + position, Ui list of U + hpos/upos in h
	findu(Ui, UPoslist),
	       %% UPoslist is position of h in g
	findg(HU, Si, G),
	       %% G with hu replace by var + hposition in a list
	findh(Vi, Ui, HU, LamH),
	       %% Use this information to check for (or find) G, H and
	       %% the Uposition.
	seqlist(Ssi, Rest, G, LamH, _, _).

 %% *************************H(U)***********************************
 %% findhu(+Ssi, +WFront/Holelist, ?H(Ui), -Ui)
 %% checks that H(Ui) is at the positions indicated by the wave fronts
 %% and returns the Ui for Ssi.
 %%
 %% Some wavefronts are contained within holes - I want to ignore
 %% them, but I want to retain the innermost hole position.
 %%
 %% Do I really want to do this ?  Surely I want Ui to equal the
 %% skeleton, ultimatly, or else I create unwanted elements in H.
findhu(_, [], [], []).
findhu(Ssi, [WF-[WHPosList]/_|WFlist], [HU-WF|HUList], [Ui|Uilist]):-
	rem_sub_wave_front(WF, WFlist, Rest, WHPosN),
	exp_at(Ssi, WF, HU),
	append(WHPosN, WHPosList, WHP),
	findui(HU, [WHP], Ui, WF),
	findhu(Ssi, Rest, HUList, Uilist).

findui(_, [], [], _).
findui(HU, [WH|WHPosList], [Ui-WF/WH|UList], WF):-
	exp_at(HU, WH, Ui),
        \+ HU = appn(_, _, Ui),
	findui(HU, WHPosList, UList, WF).

%% Some wavefronts are contained within holes - I want to ignore them
rem_sub_wave_front(_, [], [], []).
rem_sub_wave_front(Pos, [WF-[WHPosList]/_|WFlist], Out, WHPosNew):-
	append(List, Pos, WF),
        length(List, 1),
	rem_sub_wave_front(Pos, WFlist, Out, WHPos),
	append(WHPos, WHPosList, WHPosNew).
rem_sub_wave_front(Pos, [WF-[WHPosList]/HO|WFlist], [WF-[WHPosList]/HO|Out], WHPos):-
	\+ append(_, Pos, WF),
	rem_sub_wave_front(Pos, WFlist, Out, WHPos).

 %% ******************************G*******************************
 %% findg(+H(U), +Ssi, ?G)
 %% Checks that G is the term acheived by replacing H(U) in Ssi
 %% with a variable
findg([], Ssi, Ssi-[]).
findg([HU-Pos|HUlist], Ssi, G-[Pos|L]):-
	replace(Pos, Var,Ssi, GSoFar),
	findg(HUlist, GSoFar, G-L).

%% *****************************H********************************
 %% findh(+Vs, +Ui, +H(Ui), -LamH)
 %% determines the function H (in Lambda form).
findh(_, [], [], []).
findh(Vs, [Ui|Ulist], [HU-Pos|HUlist], [FH|Hlist]):-
	repu(Vs, Ui, HU, H),
	rem_var(H, FH),
	findh(Vs, Ulist, HUlist, Hlist).

%% Recurses through list of wave hole posisions and terms and replaces
%% all wave holes with variables.
repu(_, [], T, T).
repu(Vs, [Ui-_/_|UList], HU, Out):-
	replace_all(Ui, Var, HU, H),
	repu(Vs, UList, H, Out).

%%  Takes a context e.g. s(_) and removes variables to leave s
rem_var(F, F):- ground(F).
rem_var(Func, F):-
	Func =.. [F, Var],
	var(Var).
rem_var(Func, F):-
	Func =.. [Fu |Arglist],
	Fu \== of,
	delete_vars(Arglist, NewArglist),
        of(F, Fu, NewArglist).
rem_var(Func, FOut):-
	Func =.. [of, F, El],
	delete_vars(El, Out),
	\+ var(F),
        FOut =.. [of, F, Out].

delete_vars([], []).
delete_vars([H|T], NewT):-
	var(H),
	delete_vars(T, NewT).
delete_vars([H|T], [N|NewT]):-
	\+ var(H),
	rem_var(H, N),
	delete_vars(T, NewT).

of(F, Fu, [Arglist]):-
	F =.. [of, Fu, Arglist].
of(F, Fu, [H|T]):-
	\+ T = [],
	F1 =.. [of, Fu, H],
	F =.. [of|[F1|T]].

%%***********************************U***********************************
 %% findu0(+Si, +/-UPositionList, -/+Ui)
 %% Returns a list of Uis or U positions, since Ui may be several
 %% terms - see notes for examples.
 findu(A, B):-map_list(A, B, upos).

upos([], []).
upos([Ui-Pos/_|UList], [Pos|Poslist]):-
	upos(UList, Poslist).
	
findu(Term, [], []).
findu(Term, [Ui|Ulist], [UPos|UPoslist]):-
	findu2(Term, Ui, UPos),
	findu(Term, Ulist, UPoslist).

findu2(Term, [], []).
findu2(Term, [Ui|Ulist], [UPos|UPoslist]):-
	exp_at(Term, UPos, Ui),
	findu2(Term, Ulist, UPoslist).


%%***************************G(H^n(U0))***********************************
%%
%%  Form the term g(h^n(u0)) from the identified constituent parts
ghnu0(G-Pos, [H], [[U0]], Nat:pnat):-
	exp_at(G, Pos, appn(Nat, H, U0)).
ghnu0(G-[Pos], [H], [[U0]], Nat:pnat):-
	exp_at(G, Pos, appn(Nat, H, U0)).
ghnu0(Rel-PosList,  HList, UListList, Nat:pnat):-
	set_to_function(_, Rel, Term),
	ghnu0(Rel, PosList, HList, UListList, Nat).

ghnu0(_, [], [], [], _).
ghnu0(Term, [Pos|Plist], [H|Hlist], [[U]|UList], Nat):-
	exp_at(Term, Pos, appn(Nat, H, U)),
	ghnu0(Term, Plist, Hlist, UList, Nat).



%% ************************************************************************
%%  Utilities

%% replaces X with Y in A to form B  complicated by the potential
%% presence of typed terms, n:pnat and lists
repl(A, A, []).
repl(A, B, [[Y, X]|List]):-
	rl(X, Y, A, C),
	repl(C, B, List).


rl(_, _, [], []).
rl(X, Y, Term, NewTerm):-
	atomic(Term),
	Term \== [],
	replace_all(X, Y, Term, NewTerm).
rl(X, Y, Term, NewTerm):-
	\+ atomic(Term),
	\+ Term =.. [.|_],
	\+ Term = (_:_),
	replace_all(X, Y, Term, NewTerm).
rl(X, Y, Term, NewTerm:T):-
	\+ atomic(Term),
	\+ Term =.. [.|_],
	Term = (V:T),
	replace_all(X, Y, V, NewTerm).
rl(X, Y, [H|T], [NewH|NewT]):-
	rl(X, Y, H, NewH),
	rl(X, Y, T, NewT).

%% Removes any wave hole bracketting left around.
rem_brackets(Atom, Atom):-
	atomic(Atom).
rem_brackets(Var, Var):-
	var(Var).
rem_brackets(Term, NewTerm):-
	wfhole(Term, InT),
	rem_brackets(InT, NewTerm).
rem_brackets(Term, NewTerm):-
	\+ atomic(Term), \+var(Term),
	\+ wfhole(Term,_),
	Term =.. [F |Arglist],
	rblist(Arglist, NewArglist),
	NewTerm =.. [F|NewArglist].

rblist(A, B):-map_list(A, B, rem_brackets).

%%  To prevent confusing substitutions.
order_subs([], []).
order_subs([[R, O]|T], [[R, O]|T1]):-
	\+ (member([_, R], T)),
        order_subs(T, T1).
order_subs([[R, O]|T], T1):-
	member([_, R], T),
	append(T, [[sp, R, O]], NewT),
        order_subs(NewT, T1).
order_subs([[sp, R, O]|T], [[R, O]|T1]):-
	\+ (member([_, R], T)),
        order_subs(T, T1).
order_subs([[sp, R, O]|T], []):-
	member([_, R], T),
	nl, nl, write('Substitution Warning'), nl, nl.

variable_subs(Vs, [], []).
variable_subs(Vs, [[S0, S1]|T], [[S0, S1]|T2]):-
    member(S0:_, Vs),
    variable_subs(Vs, T, T2).
variable_subs(Vs, [[S0, S0]|T], T2):-
    \+ member(S0:_, Vs),
    variable_subs(Vs, T, T2).





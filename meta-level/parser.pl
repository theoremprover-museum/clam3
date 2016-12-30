% WAVE-RULE PARSER
%

:- [library(basics)].
:- [library(lists)].
:- [library(more_lists)].
:- [library(sets)].
:- [library(maplist)].
:- [library(moremaps)].
:- [library(call)].
:- [library(setof)].

add_wave_rule(Rulename,Dir) :-
  writef('adding wave-rules for %t:', [Rulename]),
  parse(Rulename, Rule, Dir, Vars),
  adjust_orient_rhs(Rule, NRule),
  wave_rule_type(NRule, Typ),
  TypDir =.. [Typ, Dir],
  replace_universal_variables(Vars, NRule, RuleSchema),
  % writef('Rule: %t \n', [RuleSchema]),
  writef('.'),
  uniq_recorda(wave,wave(Rulename,RuleSchema,TypDir),_).

replace_universal_variables(Vars, []=>Rule, []=>RuleSch):-
	replace_universal_vars(Vars, Rule, RuleSch).
replace_universal_variables(Vars, [Cond]=>Rule, [CondSch]=>RuleSch):-
	\+ Cond = [],
	replace_universal_vars(Vars, Cond-Rule, CondSch-RuleSch).

add_wave_rules(Rulename, Dir) :- add_wave_rule(Rulename, Dir),fail.
add_wave_rules(_, _):- writef('done\n').

parse(Name, Cond => WaveRule, Dir, Vars) :-
  pick_a_rule(Name, Cond => Rule, Dir, Vars),
  annotate(Rule, LHS, RHS, Vars),
  orient(LHS, RHS, AnnRule),
  convert_anns(WaveRule, AnnRule).

adjust_orient_rhs(C=>L:=>R, C=>L:=>NR):-
	wave_fronts(_, [WPos1-_/[hard,out],WPos2-_/[hard,out]], L),
        wave_fronts(BareR, [WPos-[WHPos]/[hard,out]], R),
        length(WPos1, N),
        length(WPos2, N),
        length(WPos,  N),
	wave_fronts(BareR, [WPos-[WHPos]/[hard,in]], NR),!.
adjust_orient_rhs(Rewrite, Rewrite).

wave_rule_type(_ => L :=> R, trans):-
	wave_fronts(_, WFSpecL, L),
	wave_fronts(_, WFSpecR, R),
        member(_-_/[_,out], WFSpecL),
	member(_-_/[_,in], WFSpecR),!.
wave_rule_type(_, long).

annotate(T, AL, AR, _):-                     % return admissible annotations
	getargs(T,L,R),                      % decompose into left/right parts
	pick_an(L,AL),                       % annotate left
	pick_an(R,AR),                       % annotate right 
	non_trivial(AL,AR),                  % nontrivial?  
	skel_preserving(AL,AR).              % also Skeletons equal?

annotate(T, AnnL, AnnR, Vars):-
        writef('\n Now checking for bone-loss wave-rules.\n'),
	getargs(T,L,R),                      % decompose into left/right parts
        pick_an(L, AL),                      % annotate left
        add_sinks(AL, R, AnnL, AnnR, Vars), % bone-loss required?
        skel_preserving(AnnL, AnnR).


orient(AL, AR, WRule) :-            % orient an annotated equation
  direction(Dir),                   % either out or in  (both w/ backtracking)
  set_orient(AL,OAL,Dir),           % Set direction on LHS
  maximize_orient(OAL,AR,OAR,Dir),  % Set direction on RHS
  getargs(WRule,OAL,OAR).           % recompose into a rule

% Picks all possible (maximally split) annotations
pick_an(T,T) :- 
	atomic(T), !.  % Don't annotate
pick_an(T, AT):-
	T =.. [F|Args],  
	maplist(pick_an, Args, AnArgs),   
	AT =.. [F|AnArgs].
pick_an(T,AT) :-   
	T =.. [F|Args],  
	pick_an(Args,AnArgs,0), 
	AnT =.. [F|AnArgs], 
	box(AnT,AT).

% stick a hole around at least one subterm
pick_an([],[],N) :- 
	N > 0.
pick_an([H|T1],[H|T2],N) :- 
	pick_an(T1,T2,N).
pick_an([H1|T1],[H2|T2],N) :-  
	pick_an(H1,AH1), 
	hole(AH1,H2), 
	NN is N+1, 
	pick_an(T1,T2,NN).

add_sinks(AL, R, NewL, NewR, Vars):-
        convert_anns(LHS, AL),
	\+ wave_rule(_, _, _ => LHS:=>_),
        skeleton(AL, SkelTerm),
        exp_at(R, Pos, SkelTerm),
        skeletons(AL, [SkelL]),
        locate_sinks(SkelL, SkelTerm, SubsL, SubsR, Vars),
        replace_all_list(SubsL, AL, NewL),
        replace_all_list(SubsR, SkelTerm, NSkelR),
        embed_rhs(Pos, R, NSkelR, NewR).

embed_rhs([], _, NewR, NewR):- !.
embed_rhs(Pos, R, SubR, wf(NewR,dir)):-
	replace(Pos, wh(SubR), R, NewR).
	
locate_sinks(L, R, SubsL, SubsR, Vars):-
	L =.. [F|Args1],
        R =.. [F|Args2],
        locate_sinks_list(Args1, Args2, SubsL, SubsR, Vars).

expand_sinks(R, NewR):-
	exp_at(R, Pos1, wf(T,_), WF),
	exp_at(WF, Pos2, wh(sink(_))),!,
        erase(T, ET),
        replace(Pos1, sink(ET), R, NR),
	expand_sinks(NR, NewR).
expand_sinks(NewR, NewR).

locate_sinks_list([], [], [], [], _).
locate_sinks_list([Arg|Args1], [Arg|Args2], Subs1, Subs2, Vars):- !,
	locate_sinks_list(Args1, Args2, Subs1, Subs2, Vars).
locate_sinks_list([Arg1|Args1], 
                  [Arg2|Args2], 
                  [[Arg1,sink(Arg1)]|Subs1], 
                  [[Arg2,sink(Arg2)]|Subs2], Vars):-
        \+ Arg1 = Arg2,
	member(Arg1:_, Vars),!,
        locate_sinks_list(Args1, Args2, Subs1, Subs2, Vars).
locate_sinks_list([Arg1|Args1], [Arg2|Args2], AllSubs1, AllSubs2, Vars):-
        locate_sinks(Arg1, Arg2, S1, S2, Vars),
        locate_sinks_list(Args1, Args2, Subs1, Subs2, Vars),
        append(S1, Subs1, AllSubs1),
        append(S2, Subs2, AllSubs2).

replace_all_list([], Term, Term).
replace_all_list([[H1,H2]|T], Term, NewTerm):-
	replace_all(H1, H2, Term, NTerm),
	replace_all_list(T, NTerm, NewTerm).


% Skeletons
% For Preservation we take that skeletons of LHS are subset of those on RHS
% Further, to reduce skels we insist that skels on LHS can't be further weakened
% and still have subset property.

skel_preserving(A1,A2) :-
   skeletons(A1,S1), skeletons(A2,S2),
   subset(S2,S1),!,
   \+ (weaker(A1,WA1), skeletons(WA1,WS1), subset(S2,WS1)).
skel_preserving(A1,A2) :-
  skeletons(A1,[Skel]), skeletons(A2,[Skel]).

skeletons(T,Skelset) :- 
	unannotated(T), Skelset = [T], !.    % Unannotated --- return self

skeletons(sink(T), [_]):- !.

skeletons(T,Skelset) :-                    % Wave front case
  wfholes(T,Holes),                        % list of holes
  maplist(skeletons, Holes, HoleSkels),    % skel sets for each hole
  lflatten(HoleSkels,FHoleSkels),          % flatten to list of skels
  list_to_set(FHoleSkels, Skelset), !.     % turn back into set

skeletons(T,Skelset) :-                   % Normal function case
   T =.. [F|Args],
   maplist(skeletons, Args, Skels), 
   setprod(Skels,FArgs),
   maplist(args_to_func(F), FArgs, Skelset).

args_to_func(F,L,T) :- T =.. [F|L].

% Calculate weakenings of term T  A weakening consist of taking a wave-front with
% multiple holes and removing some number of the holes.  The weakest terms
% are maximally weak. 

weaken(T,T) :- atomic(T), !.
weaken(T,Q) :- wfparts(T,F,Args,Dir), holeweak(Args,WArgs,0),
               wfparts(Q,F,WArgs,Dir).
weaken(T,Q) :- T =.. [F|Args],  maplist(weaken, Args, WArgs), Q =.. [F|WArgs].

weaker(T,Q) :- weaken(T,Q), \+ T == Q.
weakest(T,Q) :- weaken(T,Q),  \+ weaker(Q,_).

weakenings(T,S) :- set_of(W,weakest(T,W),S).

holeweak([],[], N) :- N > 0, !.    % argument so at least 1 hole remains...
holeweak([H|T1],[H|T2],N) :-  (iswh(H) -> N1 is N+1; N1 = N),
                               holeweak(T1,T2,N1).
holeweak([H1|T1],[H2|T2],N) :- wfhole(H1,H1Hole), erase(H1Hole,H2),
                               holeweak(T1,T2,N). 

% set orientation for LHS.  Could pick all 2^n possibilities.
% but for now stick with all out or all in
% flip_orient like set_orient but tries all flip combinations on backtracking.

set_orient(T,OT,out) :- map_on_tree(setout, T, OT).
set_orient(T,OT,in) :- map_on_tree(setin, T, OT).
flip_orient(T,OT) :- map_on_tree(setdir, T, OT).

% Find maximal orientation.  For inward oriented wave-fronts this is easy since
% everything on the LHS must point in and our measure must succeed.
% For Out, naively generate possible annotations with measure and return max ones.

maximize_orient(OL,R,OR,in) :- 
  map_on_tree(setin, R, OR),                      % set RHS in
  measure(in,OL,OLM),                             % Take measure of LHS
  measure(in,OR,ORM),                             % and of RHS
  mcompare(in,OLM,ORM).                           % now compare them

maximize_orient(OL,R,OR,out) :-                   
  set_of(AM, an_with_measure(R,AM),AMSet),        % set of all orientation/measures
  measure(out,OL,OLM),                            % measure of LHS
  is_max_solution(OLM,AMSet,OR).                  % Pick max solution < LHS measure

% maximal solution for out orientation

is_max_solution(Upper,Set,Max) :-     % set is annotation/measure pair
   member(pair(Max,MMax),Set),        % <Max,Max Measure> is in set
   mcompare(out,Upper,MMax),          % Measure less than that of upper
   \+ (member(pair(_,Measure),Set),   % Nothing else
       mcompare(out,Upper,Measure),   % that is less than upper
       mcompare(out,Measure,MMax)).   % but also greater than what we have

% nondeterministically return an annotation of T 
an_with_measure(T, ATWM) :- flip_orient(T,AT),  measure(out,AT,ATM),
                            pair(ATWM,AT,ATM).

% Compute measure of weakenings.  This returns list of measures
measure(Dir,T,M) :-  weakenings(T,TWS),  maplist(simple_measure(Dir),TWS,M).

% Compute measure list of simply annotated term. 
% Measure used is WIDTH measure (see CADE-12 paper) which gives each wave-front
% a weight of 1.  This measures width as wave-fronts are already maximally split.
% Note that routines work for computing both in/out measures so we pass in the
% direction Dir so we only count the appropriate fronts.

simple_measure(_,T,[0]) :- atomic(T), !.     % Atoms have weight 0

simple_measure(Dir,T,M) :-                 % wavefront with single argument
  iswf(T,Orient),
  wfholes(T,[Arg]),
  simple_measure(Dir,Arg,[AH|AT]),         
  (Dir == Orient ->  AH1 is AH + 1; AH1 = AH),   % Check that direction corresponds to
  M = [AH1|AT], !.                               % what we are measuring

simple_measure(_,T,_) :- iswh(T), write('INTERNAL ERROR!!!').   % Should never be here!

simple_measure(Dir,T,[0|MRest]) :-                % Non-wave-front functor.
  T =.. [_|Args],
  maplist(simple_measure(Dir),Args,ArgVals),      % get measures for arguments
  talley(ArgVals,[MRest]).                        % add these pointwise

% comparison --- base on multiset extension of weakening comparison 
% which is simply annotated.  Padding makes lists equal lengths by 0 padding.

simple_compare(out,SLM,SRM) :- pad(SLM,SRM,L,R),  revlex(L,R).
simple_compare(in,SLM,SRM) :- pad(SLM,SRM,L,R), lex(L,R).

mcompare(Dir,ML,NL) :-
   list2mset(ML,M),   list2mset(NL,N),
   \+ mseteq(M,N),
   forall(X/Nx,N, 
      (mmember(X/Mx,M),!,
      if(Nx>Mx,
          (thereis(Y/My,M,
                  (mmember(Y/Ny,N),
                   My > Ny,
                   simple_compare(Dir,Y, X))
                   )
         )
       ),!
      )
   ).

% pad --- 0 pads lists to make same size
pad([],[],[],[]) :- !.
pad([H1|T1],[],[H1|N1],[0|N2]) :- pad(T1,[],N1,N2).
pad([], [H2|T2],[0|N1],[H2|N2]) :- pad([],T2,N1,N2).
pad([H1|T1],[H2|T2],[H1|N1],[H2|N2]) :- pad(T1,T2,N1,N2).

% lex over lists of same size
lex([],[]) :- !, fail.
lex([H|T1],[H|T2]) :- lex(T1,T2), !.
lex([H1|_],[H2|_]) :- H1 > H2.

revlex(A,B) :- rev(A,RA), rev(B,RB), lex(RA,RB).

% Following used to weed out trivial annotation.
% It is very difficult to come up with a good definition of this!
% Below I say annotation is trivial if at any point, we have
% two identical terms, two terms with annotation at the
% same position.  I commented out the addition for "weakly trivial" which also
% insists they share the same function symbol.

triv(A,A) :- !, annotated(A).
triv(A,B) :- iswf(A),iswf(B), !,   wffunc(A,T), wffunc(B,T).
triv(A,B) :- iswf(A), (\+ iswf(B)), !, fail.
triv(A,B) :- iswf(B), (\+ iswf(A)), !, fail.
triv(A,B) :- A =.. [Fa|AArgs], B =.. [Fa|BArgs], trivlist(AArgs,BArgs).
% added to eliminate wave-rules which position fronts directly
% on constants.
triv(_,B) :- exp_at(B,_,SubB),
             iswf(SubB),
             wfholes(SubB,Holes),
             member(Hole,Holes),
             constant(Hole, _).

trivlist([H1|_],[H2|_]) :- triv(H1,H2).    % No base case... (fail)
trivlist([_|T1],[_|T2]) :- trivlist(T1,T2).

non_trivial(A,B) :- \+ triv(A,B).

%:- op(850,xfy,=>).
getargs(L:=>R,L,R).

direction(out).
direction(in).

box(T,wf(T,dir)).   % Box with a direction "dir"
hole(T,wh(T)).
wfhole(P,Q) :- hole(Q,P).
sink(T, sink(wf(T,in))).

% set directions.  For setdir we allow backtracking.
setout(X,Y) :- (X = dir -> Y = out; Y = X).
setin(X,Y) :- (X = dir -> Y = in; Y = X).
setdir(dir,out).
setdir(dir,in) :- !.
setdir(X,X).      % default to catch other constants

iswf(wf(_,_)).
iswf(wf(_,Dir),Dir).
iswh(wh(_)).
issink(sink(_)).
wfparts(wf(T,Dir),F,Args,Dir) :- T =.. [F| Args].
wffunc(W,F) :- wfparts(W,F,_,_).
wfterm(wf(T,Dir),T,Dir).
wfargs(wf(T,_),Args) :- T =.. [_| Args].
wfholes(T,Holes) :- wfargs(T,TArgs), convlist(wfhole,TArgs,Holes).
sinkterm(sink(T), T).

annotated(T) :- iswf(T), !.    % any annotation in T?
annotated(T) :- issink(T), !.
annotated(T) :- T =.. [_|Args],  some(annotated,Args).
unannotated(T) :- \+ annotated(T).

erase(T,T) :- atomic(T), !.
erase(T,Q) :- wfterm(T,Arg,_), erase(Arg,Q), !.
erase(T,Q) :- wfhole(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- sinkterm(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- T =.. [F|Args],  maplist(erase, Args, EArgs), Q =.. [F|EArgs].

% map_on_tree apply predicate to all nodes in tree T
% Can backtrack over Pred
map_on_tree(Pred,T1,T2) :- atomic(T1), !, call(Pred, T1,T2).
map_on_tree(Pred,T1,T2) :- 
   T1 =.. ExpT1, maplist(map_on_tree(Pred),ExpT1,ExpT2), T2 =.. ExpT2.

% set product takes a list of sets and returns a set of products

lflatten([],[]).
lflatten([H|T], Flat) :- lflatten(T,TFlat), append(H,TFlat,Flat).

setprod([],[[]]).
setprod([H|T],Out) :-  setprod(T,TOut), setprod(H,TOut,Out).

setprod([], _, []).  % First arg is now a set of elements 
setprod([H|T], L, Product) :-
        maplist(append([H]),L,HL),
        setprod(T,L,Rest),
        union(HL,Rest,Product).

% Talley takes list of list of values and returns list of their pointwise sums
talley([],[]).       
talley([H],[H]).
talley([H1,H2|T],R) :-  talley(H1,H2,O), talley([O|T],R).

talley([],R,R) :- !.
talley(R,[],R) :- !.
talley([H1|T1],[H2|T2],[H3|T3]) :- H3 is H1 + H2, talley(T1,T2,T3).

pair(pair(A,B),A,B).
first(pair(A,_), A).
second(pair(_,B), B).


% Multisets Utilities
% 
% Multisets are represented by unordered lists of the 
% form [El1/N1, .. Eln/Nn] where Eli are the elements
% of the multiset and Ni are the number of occurrences
% of Eli. 

mmember(El/N,M):-   member(El/N,M).
mmember(El/0,M):-  \+member(El/_,M).

munion([],M,M).
munion([El/N1|M],N,[El/N3|P]):-
     mmember(El/N2,N),
     N3 is N2 + N1,
     delete(N,El/N2,NE),
     munion(M,NE,P).

mseteq([],[]).
mseteq([El/N1|M],N):-
     member(El/N1,N),
     delete(N,El/N1,NE),
     mseteq(M,NE).

list2mset([],[]).
list2mset([El|L],M):-
     list2mset(L,N),
     munion([El/1],N,M).

list2set([],[]).
list2set([El|L],M):-
     list2set(L,N),
     union([El/1],N,M).

% Universal, Existential and Conditional meta-predicates

thereis(Var,[Var|_],Pred):-  \+ \+ Pred,!.
thereis(Var,[_|Ls],Pred):- thereis(Var,Ls,Pred).

forall(_,[],_).
forall(Elem,[L|Ls],Pred) :-
    \+ \+ (Elem = L, Pred),
    forall(Elem,Ls,Pred).

if(Test,Then):-
    Test,!,Then.
if(_,_).

pick_a_rule(RuleName, Cond => (L :=> R), Dir, Vars):-
	pick_rule(RuleName, Cond => (L :=> R), Dir, Vars),
	\+ contains_meta_variables(L).

pick_rule(RuleName, [] => (L :=> R), imp(right), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
        precon_matrix(Vars, [] => R => L, Rule),
        \+ (L = (_ = _ in _)).
pick_rule(RuleName, [] => (L :=> R), imp(left), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, [] => L => R, Rule),
        \+ (R = (_ = _ in _)).
pick_rule(RuleName, C => (L :=> R), imp(right), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, C => R => L, Rule),
	C \= [].
pick_rule(RuleName, C => (L :=> R), imp(left), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, C => L => R, Rule),
	C \= [].

pick_rule(RuleName, [] => (L :=> R), equ(right), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
        precon_matrix(Vars, [] => R = L in _, Rule).
pick_rule(RuleName, [] => (L :=> R), equ(left), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, [] => L = R in _, Rule).
pick_rule(RuleName, C => (L :=> R), equ(right), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, C => R = L in _, Rule),
	C \= [].
pick_rule(RuleName, C => (L :=> R), equ(left), Vars):-
	recorded(theorem,theorem(_, _, Rule, RuleName), _),
	precon_matrix(Vars, C => L = R in _, Rule),
	C \= [].

convert_anns(WaveTermEx, WaveTermIn):-
        \+ var(WaveTermEx),!,
        (split_wave_fronts(WaveTermEx, _, NWaveTermEx);
         NWaveTermEx = WaveTermEx),
        wave_to_wave(NWaveTermEx, WaveTermIn).
convert_anns(WaveTermEx, WaveTermIn):-
        wave_to_wave(WaveTermEx, WaveTermIn).

waves_to_waves([], []).
waves_to_waves([H1|T1], [H2|T2]):-
        wave_to_wave(H1, H2),
        waves_to_waves(T1, T2).
wave_to_wave(Var, Var) :- atomic(Var),!.
wave_to_wave('@wave_front@'(_, _, Term), wf(NTerm, dir)):- 
	\+ var(NTerm),
	functor(NTerm, HOV, _),
        is_meta_variable(HOV),!,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_front@'(_, _, Term), wf(NTerm, dir)):- 
	\+ var(Term),
	functor(Term, HOV, _),
        is_meta_variable(HOV),!,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_front@'(hard, _, Term), wf(NTerm, dir)):- !,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_front@'(_, Dir, Term), wf(NTerm, Dir)):- 
	\+ var(NTerm),
	functor(NTerm, HOV, _),
        is_meta_variable(HOV),!,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_front@'(_, Dir, Term), wf(NTerm, Dir)):- 
	\+ var(Term),
	functor(Term, HOV, _),
        is_meta_variable(HOV),!,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_front@'(hard, Dir, Term), wf(NTerm, Dir)):- !,
        wave_to_wave(Term, NTerm).
wave_to_wave('@wave_var@'(Term), wh(NTerm)):- !,
        wave_to_wave(Term, NTerm).
wave_to_wave('@sink@'(Term), sink(NTerm)):- !,
        wave_to_wave(Term, NTerm).
wave_to_wave(Term, NTerm):-
        \+ var(NTerm),!,
        NTerm =.. [F|NArgs],
        waves_to_waves(Args, NArgs),
        Term =.. [F|Args].
wave_to_wave(Term, NTerm):-
        \+ var(Term),
        Term =.. [F|Args],
        waves_to_waves(Args, NArgs),
        NTerm =.. [F|NArgs].

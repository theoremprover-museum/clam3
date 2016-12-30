/* clam.v2.4s files wave_rules.pl */


/*
 * @(#)wave_rules.pl,v 1.30 1995/10/24 14:53:17 img Exp
 *
 * wave_rules.pl,v
 * Revision 1.30  1995/10/24  14:53:17  img
 * removed old parsing code
 *
 * Revision 1.29  1995/10/18  13:23:10  img
 * Newline and eof added for SWI
 *
 * Revision 1.28  1995/10/03  13:25:51  img
 * warning message removed
 *
 * Revision 1.27  1995/08/01  08:38:38  img
 * allow multiple conditions via conjunction
 *
 * Revision 1.26  1995/07/18  18:14:15  img
 * add_wave_rule removed; speeded-up parsing of rewrite rules
 *
 * Revision 1.25  1995/05/17  02:18:03  img
 * 	* Conditional multifile declaration (for Quintus).
 *
 * Revision 1.24  1995/05/10  18:27:08  img
 * 	* reverted to version 1.21 since old parser is needed for
 * 	  reduction rules (sigh)
 *
 * Revision 1.23  1995/05/10  14:38:53  img
 * 	* typo
 *
 * Revision 1.22  1995/05/10  03:54:17  img
 * 	* Removed lots of old wave-rule junk;  some cosmetic changes
 *
 * Revision 1.21  1995/04/28  16:43:56  img
 * 	* Tidied up add_wave_rule/1;  proper_rewrite/3 checks that
 * 	  variable conditions are met;  WARNING: {true} is compound so
 * 	  could be LHS of a rewrite---maybe we need to go to the
 * 	  trouble of checking for this pseudo-atomic case?
 *
 * Revision 1.20  1995/04/25  09:40:27  img
 * 	* fast_meta_ripple/2: move wave-fronts over identical function
 * 	  symbols.  meta_ripple/3 is too slow for this purpose.
 *
 * Revision 1.19  1995/03/29  10:47:57  img
 * 	* map_list_filter added
 *
 * Revision 1.17  1995/03/01  03:42:10  img
 * 	* Cosmetic changes, removed singleton variables
 *
 * Revision 1.16  1995/02/28  02:42:13  img
 * 	* NOTE: pick_an does not add multiple holes to wave-fronts
 * 	  since it chooses a particular skeleton from Skels to work
 * 	  on.
 *
 * Revision 1.15  1995/02/28  00:20:48  img
 * 	* tidied up;  generalized some of the code by adding an
 * 	  argument indicating permissible wave-front directions
 *
 * Revision 1.14  1995/02/22  17:03:04  img
 * 	* ripple does not allow weakening;  weakening/2 plays that role
 *
 * Revision 1.13  1995/02/16  22:46:27  img
 * 	* optional code to enforce set equality of skeletons---this
 * 	  would require  weakening to be done explicitly
 *
 * Revision 1.12  1995/02/16  22:44:30  img
 * 	* re-order the clauses for pick_an so as to generate
 * 	  multi-hole solutions first (see comment there).
 *
 * Revision 1.11  1994/12/07  18:40:23  dream
 * 	* added explicit unify/2 check for soundness
 * 	* added version of replace_meta_vars which records the
 * 	  meta-variables introduced
 *
 * Revision 1.10  1994/09/30  14:07:23  dream
 * 	* changed all occurrences of copy/2 to copy_term/2
 *
 * Revision 1.9  1994/09/22  10:27:35  dream
 * 	* forgot to replace wf and wh in apply_subs!
 * 	* added add_rewrite_rule/1 to support the library interface to the
 * 	  pre-recored rewrite database.  Rewrite rules are added at
 * 	  the same time a wave-rule is parsed.
 *
 * Revision 1.8  1994/09/22  00:04:40  dream
 * 	* more (supposed) efficiency improvements: pre-compute the flag
 * 	  SinksPresent for each Skels in pick_an/4.   The idea is to
 * 	  prevent the need for a memberchk1_rec each time a sink
 * 	  annotation is to be added to a term.  The only time this flag
 * 	  needs to be updated is when we imitate and decscend recursively
 * 	  into a term (and hence similarly for the target skeleton).  This
 * 	  update is done by the map_list in map_pick_an/3 (wave_rules.pl)
 *
 * 	[ This efficiency improvement may well be made redundant if all
 * 	the rippling code is rewritten _over ground terms_. In this way the
 * 	(currently cumbersome) need for explicit id_check on sinks can
 * 	be avoided and prolog unification used to test for equality
 * 	modulo sinks. ]
 *
 * 	* removed spurious check for empty set in pick_an (wave_rules.pl)
 *
 * Revision 1.7  1994/09/21  23:17:39  dream
 * 	* really delete subset1/2 this time!
 *
 * Revision 1.6  1994/09/21  23:14:05  dream
 * 	* replaced pick_rule/5 clauses with the more familiar pre-recorded
 * 	  approach using the record database (cf. library.pl for building
 * 	  the rewrite database);  deleted the old convert_anns/2 and
 * 	  wave_to_wave code which is no longer required
 * 	* removed subset1/2 which is no longer required
 *
 * Revision 1.5  1994/09/21  21:59:28  dream
 * 	* redefined match_erasure/2 so that the erasure of LHS (in the
 * 	  body of ripple/5) need not be repeatedly computed for each
 * 	  success of pick_rule (wave_rules.pl)
 * 	* removed pick_an_pos/4, since this was unused (wave_rules.pl)
 * 	* IMPORTANT: I have propagated the convert_anns conversion code up
 * 	  into the body of the dynamic rippling, but this has the effect of
 * 	  decentralizing the representation of annotations.  This will be a
 * 	  problem when soft wave fronts are to be dealt with.  We do not yet
 * 	  have this case: THIS CODE WILL NOT WORK WITH SOFT WAVE FRONTS!
 * 	  (wave_rules.pl)
 *
 * Revision 1.4  1994/09/21  09:44:09  dream
 * 	* first version with dynamic wave-rule parsing/application
 *
 * Revision 1.3  1994/09/16  13:38:55  dream
 * 	* removed potential-waves/2
 *
 * Revision 1.2  1994/09/16  10:53:23  dream
 * 	* made singleton variables anonymous; removed some dead code
 *
 * Revision 1.1  1994/09/16  09:18:22  dream
 * Initial revision
 *
 */

/* AI. Indicates stuff commented out because it duplicates (compiled)
 * code of Andrew's (LD.)*/ 


/*
 * Dynamic wave-rule application/parsing
 * 
 * To rewrite, take term T and try to rewrite at some position T'.  Insist that
 * T' is annotated (somewhere).  Do book keeping to mark replacement position
 * using the magic of prolog meta-variables.
 * All skeleton equality is considered modulo any sinks present in WT
 * (see bb note 939).
 *
 * Kind is one of "direction_in", "direction_out" or "direction_in_or_out", 
 * this constrains the direction of the wave-fronts that will be generated:
 * eg "direction_in" means only inward wave-front will be present on NWTT.
 */
ripple(Kind,WTT,NWTT,Cond,Rn,Dir) :-		% rewrite at some (annotated) position)
    ((Kind == direction_in; 
      Kind == direction_out;			% just a check
      Kind =  direction_in_or_out) ->		% default is in_or_out
     true; clam_error('i dont recognise this kind of rippling (ripple/6)')),
    /* we may need the erasure of WTT a few times here, so fetch it first */
    erase(WTT, WTTerasure),
    pick_rule_no_unify(WTTerasure,LHS,RHS,Cond,Rn,Dir),
						% pick a rule, but dont instantiate
    superimpose(Kind,WTT,LHS,RHS,NWTT),		% perform superposition (if successful)
    sinkable(NWTT),

    skeletons(WTT,InSkels),
    skeletons(NWTT,OutSkels),			% DO NOT weaken
    same_length(InSkels,OutSkels),  

    WTTerasure = LHS.				% instantiate Cond

/*
 * NWTT is the same as WTT but the wave-measure is smaller for the
 * former, there skeletons are identical.    
 * This is really a sort of restricted difference match.  D is the 
 * predicate describing the directions permitted.
 */
meta_ripple(D,WTT,NWTT) :-
%    clam_error('meta-ripple/3 no longer implemented!'),nl.
    skeletons(WTT,S),
    erase(WTT,E),
    pick_an(no,S,E,T),
    maximize_orient(D,WTT,T,NWTT).   

fast_meta_ripple(WTT,NWTT) :-
    ann_exp_at(WTT,Pos,ST),
    ST =.. [F,'@wave_front@'(hard,out,SST)],
    SST =..  [F,'@wave_var@'(Hole)],
    SSTn =.. [F,Hole],
    STn =.. [F,'@wave_var@'(SSTn)],
    NWTTp = '@wave_front@'(hard,out,STn),
    replace(Pos,NWTTp,WTT,NWTT).
fast_meta_ripple_star(WTT,NWTT) :-
    fast_meta_ripple(WTT,NWTT).
fast_meta_ripple_star(WTT,NWTT) :-
    fast_meta_ripple(WTT,WTTp),
    fast_meta_ripple_star(WTTp,NWTT).



/* 
 * rippling with meta-rippling
 */
ripple_with_meta_ripple(D,WTT,NWTT,Cond,Rn,Dir) :-
    ripple(D,WTT,NWTT,Cond,Rn,Dir).
ripple_with_meta_ripple(D,WTTpre,NWTT,Cond,Rn,Dir) :-
    fast_meta_ripple(WTTpre,WTT),    
    ripple(D,WTT,NWTT,Cond,Rn,Dir).
%    write('CLAM: WARNING... fast-meta-rippling needed!!!'),nl.

/*
 * superimpose(Direction, T, LHS, RHS, ST)
 * T is a term, LHS and RHS the halves of an unannotated rewrite rule
 * and returns the annotated replacement ST. Direction describes the
 * direction of the generated wave-fronts on ST
 */
superimpose(Direction,T, LHS, RHS, ST) :-
    copy_an(T,LHS,ALHS,Subs),           % copy annotations and generate subs
    parse(Direction,_,ALHS,RHS,ARHS),	% find compatible RHS from annotated LHS
    apply_subs(Subs,ARHS,ST).           % Apply substitutions to parsed RHS

    
/*
 * parse takes annotated left hand side, unannotated right,
 * and annotates right.  For convenience, return the Skeletons of AL.
 * Direction describes the direction of the generated wave-fronts on AR
 */
parse(Direction,Skels,AL,R,AR) :-
    skeletons(AL,Skels),
    (memberchk1_rec('@sink@'(_),Skels)->SP=yes; % initialize the flag
                                        SP=no),
    pick_an(SP,Skels,R,A),			% annotate RHS
    maximize_orient(Direction,AL,A,AR). % Orient RHS, in/out direction

% Check if T2 matches erasure of T1 (but don't perform instantiations)]
% (this is just a quick check)
match_erasure(T2,ET) :-
    \+ \+ ET = T2.

% Picks all possible (maximally split) annotations
/* try to improve efficiency by looking at the list of skeletons */
pick_an(yes,_Skels,T,'@sink@'(T)).
    /* T can only be a sink if one of the skeletons is a sink too */

pick_an(_SinksPresent,Skels,T,T) :-
    /* an atomic can only be unannotated if it appears in a skeleton */
    \+ compound(T),!,
    member1(T,Skels),!.
pick_an(_SinksPresent,Skels,T,AT) :- 
    %% filter out all functors in Skels which are different from 
    %% F, since these must be hidden, and this clause is in the business of
    %% imitation.  If there are no skeletons in Skels which have F as a top-level
    %% then we must hide, since imitation is pointless.  Note that we cannot commit
    %% either way (hide/imitate) in the case of same functor, since both are
    %% required for completeness.
    %% 
    %% SinksPresent is irrelevant here since we need to recompute that
    %% for each of the  subskeletons of Skels which partially match F.
    %% (This is done in map_pick_an)
    T =.. [F|Args], 
    setof(FArgs,	
	    (member(Skel,Skels),
		  compound(Skel),
		  Skel =.. [F|FArgs]),		% preserve all which can imitate
	  FilteredSkels),			% all the argument skeletons
    map_pick_an(FilteredSkels, Args, AnArgs), 
    AT =.. [F|AnArgs].

    /* this clause is in the business of hiding F.  In the case of different
     * functors, we must hide for skeleton preservation but, as above, for
     * identical functors we can do either.  So in this case we cant constrain, since
     * hiding preserves skeletons.  Since Skels is preserved, so is SinksPresent.
     */
pick_an(SinksPresent,Skels,T,AT) :-
    T =.. [F|Args],
    pick_an(SinksPresent,Skels,Args,AnArgs,0),  % hole-ize and recursively annotate
    AnT =.. [F|AnArgs],
    box(AnT,AT).

% stick a hole around at least one subterm
/* I don't know the best order of these clauses.  Putting the H-H clause second
 * has the effect of returning weaker solutions first (terms are left unannotated),
 * putting the H1-H2 clause second and the H-H clause last adds as much annotation
 * as is possible.  The current setup is an attempt to mimic clam 2.1 behaviour, 
 * at least as I observed it planning rotlen (img/mrg/feb95), that is, weakenings 
 * (if there are any) on backtracking.
 */
pick_an(_SinksPresent,_Skels,[],[],N) :- N > 0.
pick_an(SinksPresent,Skels,[H1|T1],[H2|T2],N) :-
    pick_an(SinksPresent,Skels,H1,AH1),
    hole(AH1,H2), 
    NN is N+1, 
    pick_an(SinksPresent,Skels,T1,T2,NN).
pick_an(SinksPresent,Skels,[H|T1],[H|T2],N) :-
    pick_an(SinksPresent,Skels,T1,T2,N).

/* FilteredSkels is a list of lists of skeletons; each sublist corresponds to 
 * a possible skeleton of the corresponing element of Args
 */
map_pick_an(FilteredSkel, Args, AnArgs) :-
    nary_zip(FilteredSkel,ArgsSkels),
    map_list(ArgsSkels, I:=>O, 
	     (memberchk1_rec('@sink@'(_),I)->O=yes; O=no),
	     SinksPresentList),
    maplist(pick_an, SinksPresentList, ArgsSkels,Args, AnArgs).

nary_zip([[]|_],[]).
nary_zip(L1,[Cars|Rest]) :-
    strip(L1,Cars,NewL1),
    nary_zip(NewL1,Rest).

strip([], [], []).
strip([[H|T] | Rest] , [H|Cars], [T|Trest]) :-
    strip(Rest, Cars, Trest).


% Routines to copy annotations and apply substitutons.  Recall that
% rewrite rules use Prolog variables as match variables.  We can't use this
% though as our matching/substitution is not the standard one. 

% copy_an(+A,+Pat,-APat,-Sub) 
% Preconditions: A is well-annotated and its erasure matches Pat
% Depends on depend on 1 functor thick normal form so that we
% do not pick up substitution '@wave_var@'(...)/X where '@wave_var@'(...) is not a WAT
%
% We move the annotations from A onto Pat (in result APat).  As we reach
% the leaves of Pat we generate a substitution Sub.  Note that the ordering of
% these clauses matters and junk will be generated if preconditions are not met.
% 
% Use auxilliary bit to keep track of wf/sk (wavefront or skel)

copy_an(A,Pat,APat,Sub) :- copy_an(A,Pat,APat,Sub,sk).

copy_an(A,Pat,APat,Sub,wf) :-    iswh(A,A1), !,        % A is wh
  iswh(APat,APat1),                                    % copy over
  copy_an(A1,Pat,APat1,Sub,sk).                        % recurse

copy_an('@sink@'(A),Pat,'@sink@'(Pat),[sub(Pat,A,St)],St) :-
    St == sk,
    var(Pat), !.      % Pat is a var
/* I can't think of a reason not to allow sinks around constants! */
copy_an('@sink@'(A),B,'@sink@'(BB),Sub,St) :-
    St == sk,
    copy_an(A,B,BB,Sub,St).
copy_an('@sink@'(A),Pat,'@sink@'(Pat),[sub(Pat,A,St)],St) :-
    St == wf,!,
    clam_error('INTERNAL ERROR (copy_an) sink in wave-front').

copy_an(A,Pat,Pat,[sub(Pat,A,St)],St) :-  var(Pat), !.      % Pat is a var

copy_an(A,Pat,Pat,[],_) :- atomic(A), !,             % A is atom (so should Pat!)
  (atomic(Pat) -> true ; clam_error('INTERNAL ERROR (copy_an)')).

copy_an(A,Pat,APat,Sub,sk) :-    wfterm(A,A1,Dir), !,    % A is wf
  wfterm(APat,APat1,Dir),                                % copy over
  copy_an(A1,Pat,APat1,Sub,wf).                          % recurse

copy_an(A,Pat,APat,Sub,St) :-                            % other functor
  A =.. [F|Args],
  Pat =.. [F|PArgs],
  copy_args(Args,PArgs,APargs, Sub,St),
  APat =.. [F|APargs].
  
copy_args([],[],[],[],_).

copy_args([A|AR],[PA|PAR],[APA|APAR],S,St) :-
  copy_an(A,PA,APA,S1,St),
  copy_args(AR,PAR,APAR,SN,St),
  merge_subs(S1,SN,S).

% Two instances of X must have same skeleton
% If one is annotated and the other isn't, you can merge provided unannotated
% var is in a wave-front

merge_subs([],S,S).

merge_subs([sub(V,T,St)|R],S1,S2) :-
  sub_lookup(V,T1,St1,S1), !, 
  merge_subs(V,T,T1,St,St1,R,S1,S2).

merge_subs([H|R],S1,[H|S2]) :- merge_subs(R,S1,S2).

merge_subs(_,T,T1,wf,wf,R,S1,S2) :- !, T == T1, merge_subs(R,S1,S2).

merge_subs(_,T,T1,sk,sk,R,S1,S2) :- !, T == T1, merge_subs(R,S1,S2).

merge_subs(_,T,T1,wf,sk,R,S1,S2) :- !,  erase(T1,ET1), T == ET1, merge_subs(R,S1,S2).

merge_subs(V,T,T1,sk,wf,R,S1,S2) :- !, 
  ((unannotated(T) ->  T == T1, merge_subs(R,S1,S2));
  (erase(T,ET), ET == T1, S2 = [sub(V,T,sk)|NS2],
    delete(S1,sub(V,T1,wf),NS1), merge_subs(R,NS1,NS2))).

sub_lookup(V,T,St,Sub) :-   member(sub(V1,T,St),Sub), V == V1.   % Need "=="

% apply_subs(Subs,Pat,Res)
% apply substitution Subs to annotated pattern, resulting in Res.
% Unfortunately can't use normal Prolog unification as we must strip
% annotation when substituting into wave-fronts.

apply_subs(Subs,Pat,Res) :-
    status_tree_map(ap_sub(out,Subs),ap_sub(in,Subs),Pat,Res).

ap_sub(Status,Subs,Leaf,Res) :-
  (sub_lookup(Leaf,T,_,Subs) -> 
     (Status == in -> erase(T,Res) ; Res = T) ;
     Res = Leaf).

skeletons(T,Skelset) :-
    unannotated(T), Skelset = [T], !.		% Unannotated --- return self

/* we keep the skeleton of a sink around and try to use it later
 * when camparing skeletons then, we allow '@sink@'(X) and '@sink@'(Y) to
 * match, even when X and Y are different (this is what I mean by 
 * "modulo sinks" in the preamble of this file).
 */ 
skeletons('@sink@'(Arg),['@sink@'(Arg)]) :- !.		% sink case

skeletons(T,Skelset) :-				% Wave front case
  wfholes(T,Holes),				% list of holes
  maplist(skeletons, Holes, HoleSkels),		% skel sets for each hole
  lflatten(HoleSkels,Skelset),			% flatten to list of skels
  !.   

skeletons(T,Skelset) :-				% Normal function case
   T =.. [F|Args],
   maplist(skeletons, Args, Skels), 
   setprod(Skels,FArgs),
   maplist(args_to_func(F), FArgs, Skelset).

args_to_func(F,L,T) :- T =.. [F|L].

% Calculuate weakenings of term T  A weakening consist of taking a wave-front
% w/ multiple holes and removing some holes.  Weakest terms  are maximally weak. 

weaken(T,T) :- \+ compound(T), !.
weaken(T,Q) :- wfparts(T,F,Args,Dir), holeweak(Args,WArgs,0),
               wfparts(Q,F,WArgs,Dir).
weaken(T,Q) :-
    T =.. [F|Args],  
    maplist(weaken, Args, WArgs), Q =.. [F|WArgs].

%% IA. weaker(T,Q) :- weaken(T,Q), \+ T == Q.
%% IA. weakest(T,Q) :- weaken(T,Q),  \+ weaker(Q,_).

%% IA. weakenings(T,S) :- setof(W,weakest(T,W),S).

holeweak(A,B, C) :-
    holeweak(A,B,C,0).

% argument so at least 1 hole remains, and at least 1 hole removed
holeweak([],[], N, M) :- 
    N > 0, M > 0,!.    
holeweak([H|T1],[H|T2],N,M) :-			% keep a hole/keep a non-hole
    (iswh(H) -> N1 is N+1 ; N1 is N),
    holeweak(T1,T2,N1,M).
holeweak([H1|T1],[H2|T2],N,M) :-		% drop a hole
    striphole(H1,H1Hole),
    erase(H1Hole,H2),
    M1 is M+1,
    holeweak(T1,T2,N,M1). 

% Orientation routines.  To find maximal orientation generate (naively)
% all  possible annotations with measure and return max ones.  Only directions
% satisfying the predicate Direction are tried.

maximize_orient(Direction,OL,R,OR) :-                   
  setof(AM, an_with_measure(Direction,R,AM),AMSet),	
						% set of all orientation/measures
  measure(OL,OLM),				% measure of LHS
  max_solution(OLM,AMSet,OR).			% Pick max solution < LHS measure

% maximal solution for out orientation

max_solution(Upper,Set,Max) :-			% set is annotation/measure pair
   member(pair(Max,MMax),Set),			% <Max,MMax> Measure in set
   mcompare(Upper,MMax),			% Measure less than that of upper
   \+ (member(pair(_,Measure),Set),		% Nothing else
       mcompare(Upper,Measure),			% that is less than upper
       mcompare(Measure,MMax)).			% but also greater than what we have

% nondeterministically return an annotation of T 
an_with_measure(Direction,T, ATWM) :-
    flip_orient(Direction,T,AT),
    measure(AT,ATM),
    pair(ATWM,AT,ATM).

measure(T,M) :-					% in/out pair of weakenings measures
   weakenings(T,TWS),				% compute all weakenings
   maplist(simple_measure(out),TWS,Mout),	% compute out measures
   maplist(simple_measure(in),TWS,Min),		% compute in measures
   pair(M,Mout,Min).				% pair them

% Compute measure list of simply annotated term. 
% Measure used is WIDTH measure (see CADE-12 paper) which gives each wave-front
% a weight of 1.  This measures width as wave-fronts are already maximally split.
% Note that routines work for computing both in/out measures so we pass in the
% direction Dir so we only count the appropriate fronts.

simple_measure(_,T,[0]) :- \+ compound(T), !.     % Atoms have weight 0

simple_measure(Dir,T,M) :-                 % wavefront with single argument
  iswf(T,Orient),
  wfholes(T,[Arg]),
  simple_measure(Dir,Arg,[AH|AT]),         
  (Dir == Orient ->  AH1 is AH + 1; AH1 = AH),   % Check that direction corresponds to
  M = [AH1|AT], !.                               % what we are measuring

simple_measure(_,T,_) :- 
    iswh(T), 
    clam_error('INTERNAL ERROR (measure)').	% Shouldn't happen

simple_measure(Dir,T,[0|MRest]) :-                % Non-wave-front functor.
  T =.. [_|Args],
  maplist(simple_measure(Dir),Args,ArgVals),      % get measures for arguments
  talley(ArgVals,[MRest]).                        % add these pointwise

% measure compare.  Compare lexicographically,  (Note ordering of clauses significant!)

mcompare(pair(O1,_),pair(O2,_)) :-  multi_greater(out,O1,O2), !.
mcompare(pair(O1,I1),pair(O2,I2)) :-  
   \+ multi_greater(out,O2,O1),                      % hence they have equal measure
   multi_greater(in,I1,I2).                          % so check inner measurement

% compare using multiset extension of simple ordering

multi_greater(Dir,ML,NL) :-
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

% Simple comparison is lex or revlex.  Pad to make lists equal length.

simple_compare(out,SLM,SRM) :- pad(SLM,SRM,L,R),  revlex(L,R).
simple_compare(in,SLM,SRM) :- pad(SLM,SRM,L,R), lex(L,R).

/* AI.
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
*/
% Functions for handling orientation direction, annotation decomposition
% Note that variables in terms may be Prolog variables and these shouldn't
% be instantiated by tests/decomposition.  Hence sometimes I must use == and
% novar.  Don't mess with these!

/* DANGER: these predicate names are overloaded as flags to the
 * various methods, so if they are changed here, they must also be
 * changed there too!  (this is just to save mapping flags).
 */
direction_in_or_out(out).
direction_in_or_out(in).
direction_out(out).
direction_in(in).

/* flip_orient(Direction,T,T') 
 * T and T' are the same, only all wave-fronts in T' have a direction X
 * whilst all those in T are anonymous (ie. "dir"), such that
 * Direction(X) is satisfied.  Typically, Direction(in) and Direction(out)
 * will hold, but other possibilties are useful too (eg restriction to "out"
 * only).
 */
flip_orient(_Direction,T,T) :-
    \+ compound(T),!.
flip_orient(Direction,WF,NewWF) :-
    wfparts(WF,F,Args,Dir),			% a wave-front here
    !,
    (var(Dir) -> clam_error('Why is this a variable? (flip_orient)');true),
    D =.. [Direction,NewDir], call(D),		% get the direction
    maplist(flip_orient(Direction),Args,NArgs),
    wfparts(NewWF,F,NArgs,NewDir).
flip_orient(Direction,T,NT) :-
    T =.. [F|Args],
    maplist(flip_orient(Direction),Args,NArgs),
    NT =.. [F|NArgs].

box(T,'@wave_front@'(hard,dir,T)).   % Box with a direction "dir"
hole(T,'@wave_var@'(T)).

make_sink(T,'@sink@'(T)).

%% AI. wfhole(P,Q) :- hole(Q,P).
striphole(X,Y) :- nonvar(X), '@wave_var@'(Y) = X.
stripsink(X,Y) :- nonvar(X), '@sink@'(Y) = X.

iswf(X) :- nonvar(X), X = '@wave_front@'(hard,_,_).
iswf('@wave_front@'(hard,Dir,_),Dir).

issink(X) :- nonvar(X), X = '@sink@'(_).
issink('@sink@'(X),X).

iswh(X) :- nonvar(X), X = '@wave_var@'(_).
iswh('@wave_var@'(A),A).

/* sinkparts('@sink@'(Arg),Arg). */
wfparts(X,F,Args,Dir) :- X = '@wave_front@'(hard,Dir,T), T =.. [F| Args].
%% AI. wffunc(W,F) :- wfparts(W,F,_,_).
wfterm('@wave_front@'(hard,Dir,T),T,Dir).
wfargs('@wave_front@'(hard,_,T), Args) :- T =.. [_| Args].
wfholes(T,Holes) :- wfargs(T,TArgs), convlist(striphole,TArgs,Holes).

annotated(T) :- \+ compound(T), !, fail.    % T have anny annotation?
annotated(T) :- iswf(T), !.   
annotated(T) :- issink(T), !.
annotated(T) :- T =.. [_|Args],  somechk(annotated,Args).
unannotated(T) :- \+ annotated(T).

/*
 * erase(+P,-Q) Q is P with all annotation removed
 */
erase(T,T) :- \+ compound(T), !.
erase(T,Q) :- wfterm(T,Arg,_), erase(Arg,Q), !.
erase(T,Q) :- striphole(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- stripsink(T,Arg), erase(Arg,Q), !.
erase(T,Q) :- T =.. [F|Args],  maplist(erase, Args, EArgs), Q =.. [F|EArgs].

% sink stuff    represent sink as functor "sink"  (Admittedly not creative!)
% sinkable if term has no inward wavefront that does not have sink beneath

sink('@sink@'(_)).  

sinkable(T) :- \+ compound(T), !.       
sinkable(T) :-  % don't bother discriminating holes from non-holes
    wfterm(T,ST,out), !, sinkable(ST).  
sinkable(T) :-  % recursive call as there could be nested fronts!
    wfterm(T,ST,in), !, sinkwithin(ST), sinkable(ST).
sinkable(T) :-  T =.. [_|Args],  all(sinkable,Args).

sinkwithin(T) :- \+ compound(T), !, fail.
sinkwithin(T) :- sink(T), !.
sinkwithin(T) :- T =.. [_|Args], somechk(sinkwithin,Args).

all(_,[]).
all(P,[H|T]) :- call(P,H), all(P,T).

% map_on_tree apply predicate to all nodes in tree T
% Can backtrack over Pred
map_on_tree(Pred,T1,T2) :- \+ compound(T1), !, call(Pred, T1,T2).
map_on_tree(Pred,T1,T2) :- 
   T1 =.. ExpT1, maplist(map_on_tree(Pred),ExpT1,ExpT2), T2 =.. ExpT2.

% same as above except with 2 functions one for applications to leaves
% within wave-fronts, other within skeleton.  Use flag to toggle cases.  
% NOTE: makes syntactic assumption about names of wave-front/hole functors!
% in/out mean in wave-front or out of wave front

status_tree_map(Op,Ip,T1,T2) :- status_map(out,Op,Ip,T1,T2).

status_map(S,OP,IP,T1,T2) :- \+ compound(T1), !,
 (S == out ->  call(OP, T1,T2); call(IP,T1,T2)).

status_map(S,OP,IP,T1,T2) :-   T1 =.. ExpT1, [H|_] = ExpT1,
 (H == '@wave_front@' -> NS = in; (H == '@wave_var@' -> NS = out; NS = S)),
 maplist(status_map(NS,OP,IP),ExpT1,ExpT2), T2 =.. ExpT2.

% set product takes a list of sets and returns a set of products
/* AI.
lflatten([],[]).
lflatten([H|T], Flat) :- lflatten(T,TFlat), append(H,TFlat,Flat).

setprod([],[[]]).
setprod([H|T],Out) :-  setprod(T,TOut), setprod(H,TOut,Out).

setprod([], _, []).  % First arg is now a set of elements 
setprod([H|T], L, Product) :-
        maplist(append([H]),L,HL),
        setprod(T,L,Rest),
        append(HL,Rest,Product).

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

% Universal, Existenial and Conditional meta-predicates

thereis(Var,[Var|_],Pred):-  \+ \+ Pred,!.
thereis(Var,[_|Ls],Pred):- thereis(Var,Ls,Pred).

forall(_,[],_).
forall(Elem,[L|Ls],Pred) :-
    \+ \+ (Elem = L, Pred),
    forall(Elem,Ls,Pred).

if(Test,Then):-
    Test,!,Then.
if(_,_).
*/
/*
 * changed by img to allow wild-cards for sinks
 * examine term structure and do an id check unless we are  looking at a wildcard
 */
memberchk1_rec(X, [Y|_]) :- id_check(X,Y),!.
memberchk1_rec(X, [_|L]    ) :- memberchk1_rec(X, L).

/* checks that two terms are identical, modulo sinks */
id_check(X,Y) :-
/* variables match only if identical */
    (var(X);var(Y)),!,
    X == Y.
id_check(X,Y) :-
/* atomics match only if identical */
    (atomic(X);atomic(Y)),!,
    X == Y.
id_check(X,Y) :- 
/* two sinks match up, but we dont require that their innards match.
 * We know that X and Y are not variables in this clause, so OK to use
 * unification here 
 */
    X = '@sink@'(_),
    Y = '@sink@'(_),!.
id_check(X,Y) :-
    X =.. [F|ArgsX],
    Y =.. [F|ArgsY],
    id_check_map(ArgsX,ArgsY).

id_check_map([],[]).
id_check_map([X|ArgsX],[Y|ArgsY]) :-
    id_check(X,Y),
    id_check_map(ArgsX,ArgsY).

memberchk1(X, [Y|_]    ) :- X == Y, !.
memberchk1(X, [_|L]    ) :- memberchk1(X, L).

member1(X, [Y|_]    ) :- X == Y.
member1(X, [_|L]    ) :- member1(X, L).

/* extract a rule from the pre-recorded rewrite database. */
pick_rule(LHS, RHS, Cond, Rulename, Dir) :-
    recorded(rewrite,rewrite(LHSproper,RHS,Cond,Dir,Rulename),_),
    unify(LHSproper,LHS).

/* extract a rule from the pre-recorded rewrite database, 
 * speedy version  */
pick_rule_speedy(LHS, RHS, Cond, Rulename, Dir) :-
    copy_term(LHS,LHScopy),
    recorded(rewrite,rewrite(LHScopy,  _,_,Dir,Rulename),Ref),
    recorded(rewrite,rewrite(LHSproper,RHS,Cond,Dir,Rulename),Ref),
    unify(LHSproper,LHS).

/* extract a rule from the pre-recorded rewrite database.  unify/2 is
 * used since LHS may contain multiple occurrences of same variable.
 * LHS is _not_ instantiated, as is required in ripple/5.
 * Speedy version tries to use the reference to get quick access to
 * the `approximate' solution.  */
pick_rule_no_unify(WTTerasure,LHS, RHS, Cond, Rulename, Dir) :-
    copy_term(WTTerasure,LHScopy),
    recorded(rewrite,rewrite(LHScopy,  _,_,Dir,Rulename),Ref),
    recorded(rewrite,rewrite(LHS,RHS,Cond,Dir,Rulename),Ref),
    \+ \+ unify(LHS,WTTerasure).			% just check


/* Add as many rewrite rules as can be squeezed out of theorem
 * Rulename.  */ 
add_rewrite_rules(Rulename) :- add_rewrite_rule(Rulename),fail.
add_rewrite_rules(_).

/* Replace Universal Vars code removed */

/*
 * 3. Code for abstracting away the implementation of wave fronts.
 * 
 */

/*
 * The main predicate below, wave_fronts/3, provides a form of 
 * abstract-datatyping for wave-fronts. Nowhere else in the code should
 * the therms '@wave_front@'/3 and '@wave_var@'/1 appear.
 * 
 * Wave fronts are represented as tags inside a formula: a '@wave_front@'/3
 * tag signifies a wave-front and a '@wave_var@'/1 tag signifies a hole in 
 * the wave-front. This corresponds (roughly) to the underline-notation
 * AlanB developed on paper.
 *
 * Ideally, I would like to have this all done in one predicate usuable
 * in different modes, but somehow I can't get that to work. At the
 * moment, we do have indeed have one predicate, which forks out into
 * two different (but very similar) pieces of code depending on the
 * call-mode (delete_wave_fronts/3 and insert_wave_fronts/3)
 */

        % wave_fronts(T,L,TT): TT is equal to T
        % except that it has wave-fronts in positions specified by L.
        %
        % The elements of L are of the form 
	%
	%                    FrontPos-TermPosList/[Typ,Dir] 
        %
        % where FrontPos is a list specifying the position of the wave front
        % and TermPosList is a list of positions specifying the wave
        % terms in the wave front. Typ and Dir denote the type (soft/hard)
        % and direction (in/out) of the wave front respectively.
        % NOTE: The positions in TermPosList are relative to FrontPos.
        % EXAMPLE: the following term in underline-notation:
        %       plus(X,B)
        %       ----- - -
        % looks like: 
        %
        %    '@wave_front@'(T,D,plus('@wave_var@'(X),'@wave_var@'(B))).
        %
        % Pretty-print clauses are provided (via the portray clauses in
        % util.pl). '@wave_front@'(T,D,X) terms (the wave-fronts) are printed 
        % as ``X''<T/D>, and '@wave_var@'(X) terms (the wave-variables) 
        % are printed as {X}.
        % Thus, the above term would print as ``plus({X},{B})''<T/D>.
        %
        % Different modes of this predicate can than be used for finding
        % wave-fronts (wave_fronts(_,-,+)), deleting wave-fronts (mode
        % wave_fronts(-,+,+)), and inserting wave-fronts (mode
        % wave_fronts(+,+,-)).
        % (In fact, these are the minimally required modes. Thus, either
        % the third or the first and second argument need to be
        % instantiated). 
wave_fronts(T,L,TT) :- \+ var(TT), !, delete_wave_fronts(TT,L,T).
wave_fronts(T,L,TT) :- \+ var(T), \+ var(L), !, insert_wave_fronts(T,L,TT).

        % Following are the auxiliary predicates for wave_fronts/4,
        % All of this code is extremely tedious and boring. It's all of
        % the flavour: iterate over list, recursively descend down
        % terms, and do your thing...
        %
        % delete_wave_fronts(+Term,?List,?Term1): Term1 is like Term
        % except that it has wave-fronts deleted at positions
        % specified in List.
        % delete_wave_fronts/4 does the real work: the second argument
        % keeps track of the current position while recursively
        % descending down the term. If we hit a wave-front we delete it
        % and return the current position and term (after removing the
        % wave-variables). 
delete_wave_fronts(Term,FrontsList,Term1) :-
    delete_wave_fronts(Term,[],FrontsList,Term1).
delete_wave_fronts(T,_,L,T1) :- (atomic(T);var(T)), !, T=T1, L=[].
delete_wave_fronts('@wave_front@'(Typ,Dir,T),L,[L-WVarList/[Typ,Dir]|T1FrontsList],T2) :- !,
    delete_wvars(T,[],WVarList,T1),
        % wave fronts can be nested. The following recursive calls
        % removes nested wave-fronts:
    delete_wave_fronts(T1,L,T1FrontsList,T2).
delete_wave_fronts('@sink@'(T),L,LL,'@sink@'(TT)):- !,
	delete_wave_fronts(T,L,LL,TT).
delete_wave_fronts([H|T],[N|L],Ls,[HH|TT]) :- !,
    delete_wave_fronts(H,[N|L],L1s,HH),
    N1 is N+1,
    delete_wave_fronts(T,[N1|L],L2s,TT),
    append(L1s,L2s,Ls).
delete_wave_fronts(T,Lin,Lout,TT) :-
    T =.. [F|Args],
    delete_wave_fronts(Args,[1|Lin],Lout,Args2),
    TT =.. [F|Args2].
        % delete_wvars/4: auxiliary predicte to delete_wave_fronts. It
        % removes wave-vars in much the same way as
        % delete_wave_fronts/4 removes wave-fronts. 
         % Note the clause to ignore wave-variables that appear within
         % nested wave-fronts.  These latter can appear due to substitutions etc
         % in the planning process.
delete_wvars(T,_,L,T1) :- (atomic(T);var(T)), !, T=T1, L=[].
delete_wvars('@wave_var@'(T),L,[L],T) :- !.
delete_wvars('@wave_front@'(Typ,Dir,T),_,[],'@wave_front@'(Typ,Dir,T)) :- !.
delete_wvars([H|T],[N|L],Ls,[HH|TT]) :- !,
    delete_wvars(H,[N|L],L1s,HH),
    N1 is N+1,
    delete_wvars(T,[N1|L],L2s,TT),
    append(L1s,L2s,Ls).
delete_wvars(T,Lin,Lout,TT) :-
    T =.. [F|Args],
    delete_wvars(Args,[1|Lin],Lout,Args2),
    TT =..[F|Args2].
        % insert_wave_fronts(+Term,+List,?Term1): Term1 is like Term
        % except that is has wave-fronts inserted at positions specified
        % in List.
        % insert_wave_fronts/3 just iterates insert_wave_fronts/4 over
        % the elements of List.
        % insert_wave_fronts/4 does the real work: First insert the
        % '@wave_var@'/1 terms as specified (remember that the positions
        % of the '@wave_var@'/1s are relative to the position of the
        % '@wave_front@/3), then insert the '@wave_front@/3 at the
        % specified position. 
        % 
        % The first clause is normal termination of iteration of the
        % wave-front list, the fourth clause is the normal step-clause,
        % and the second clause catches the special case when '@wave_front@'/3
        % term and '@wave_var@'/1 term are immediately adjacent. This case is
        % "nonsensical". Such specifications can sometimes be generated
        % by calling code (e.g. in is_a_wave_rule/6), but are just
        % ignored here. Similarly, a wave-front with no '@wave_var@'s in
        % it is equally non-sensical, and caught by the third clause.
insert_wave_fronts(Term,[],Term).
insert_wave_fronts(Term,[_-[[]]/_|FrontsList],Term1) :- !,
    insert_wave_fronts(Term,FrontsList,Term1).
%insert_wave_fronts(Term,[_-[]|FrontsList],Term1) :- !,
%   insert_wave_fronts(Term,FrontsList,Term1).
insert_wave_fronts(Term,[Front-WVarList/[Typ,Dir]|FrontsList],Term2) :-
    insert_wave_fronts(Term,Front,WVarList,Typ,Dir,Term1),
    insert_wave_fronts(Term1,FrontsList,Term2).
insert_wave_fronts(Term,FrontPos,VarPosList,Typ,Dir,FrontTerm) :-
    map_list(VarPosList, Relative:=>Absolute,
            append(Relative,FrontPos,Absolute),
            NewVarPosList), 
    insert_wvars(Term,NewVarPosList,VarTerm),
    exp_at(VarTerm,FrontPos,FrontArg),
    replace(FrontPos,'@wave_front@'(Typ,Dir,FrontArg),VarTerm,FrontTerm).
insert_wvars(Term,[],Term).
insert_wvars(Term,[VarPos|VPs],VarTerm) :-
    exp_at(Term,VarPos,VarArg),
    replace(VarPos,dummy(VarArg),Term,VarTerm1),
    replace([0|VarPos],'@wave_var@',VarTerm1,VarTerm2),
    insert_wvars(VarTerm2,VPs,VarTerm).

/*
 * 4. Code for joining and splitting wave fronts.
 * 
 */

/*
 * These predicates are needed because sometimes we must split wave
 * fronts in order to apply a wave rule. The most obvious example of
 * this occurs in the evenp theorem. After induction, we end up with
 * even(plus(``s(s({x}))''<hard,out>,y)) In order to apply the step rules for
 * plus/2, we need to split up the ``s(s({x}))''<hard/out> wave front into
 * ``s({``s({x})''<hard/out>})''<hard/out>. After rippling the separate 
 * s/1's over the plus,
 * we need to join the wave fronts in the resulting term:
 * even(``s({``s({plus(x,y)})''<hard/out>})''<hard/out>) into 
 * even(``s(s({plus(x,y)}))''<hard/out>)
 * in order to ripple the two s/1's simulataneously over the even/1.
 *
 * It would have been nicer if it had been possible to write all this
 * code using the abstract representation of wave fronts implemented in
 * section 4. above. However, I found this very hard, if not impossible
 * to do. As a result, the code below for splitting/joining wave fronts
 * is written using the implementation of wave fronts in terms of
 * '@wave_front@/3 and '@wave_var@'/1 terms.
 * 
 */

        % split_wave_fronts(+Term,?PosList,?SplitTerm):
        % SplitTerm will be as Term, but with a number of complex wave
        % front split into smaller ones. PosList will contain the
        % positions of the wave fronts in Term which were split.
        % 
        % This predicate generates on backtracking all possible splits
        % of all wave fronts.
        %
        % This code deliberately returns the possible splits in a
        % sensible order: it returns the splits in bigger chunks (ie.
        % few splits) before splits in smaller chungs (since this
        % favours wave rules that ripple large wave fronts over wave
        % rules that ripple small wave fronts)).
        %
        % The algorithm for producing the split wave fronts is as follows:
        % (Algorithm design courtesy of Andrew Stevens):
        % 
        %  [1] pick any number of splittable ``...''s, and for any of
        %      these do the following: 
        %  [2] label all terms spanning the {...}'s of the ``...''
        %      picked in [1] 
        %      (that is, not including {...}'s part of other ``...''s,
        %       whether nested in the term picked at [1] or not)
        %      (these terms are exactly those where possible wave front
        %       splits can be introduced)
        %  [3] descend down all the subterms of the ``...'' chosen in [1],
        %      while for each doing the following:
        %      [i]   if un-labelled term, return term
        %      [ii]  if {...}, return term (subsumed by [i])
        %      [iii] if labelled term then do one of the following:
        %            [a] un-label term, and repeat [3] for this term
        %            [b] - change label to {``...''}
        %                  (ie insert new wave front), then 
        %                - remove all labels from subterms, then
        %                - return
        %
        % This algorithm is non-deterministic in two places, namely step
        % [1] and step [3][iii]
split_wave_fronts(In,PosL,Out) :-
        % Step [1]:
    findall(FrontPos-VarPosL-[Typ,Dir]-FTerm,
            pick_deep_wave_front(In,FrontPos,VarPosL,'@wave_front@'(Typ,Dir,FTerm)),
            FrontsTerms),
    subseq(FrontsTerms,[SomeFr|OntsTerms],_),
        % Step [2]-[3]:
    map_list([SomeFr|OntsTerms],
            (FrontPos-VarPosL-TypDir-FTerm):=>(FrontPos-SplitSubTerm),
            split_one_wave_front(FTerm,VarPosL,TypDir,SplitSubTerm),
            FrontPosSplitSubTerms),
        % Do the final replacement into the output term:
    SomeFr = (_-_-[Typ,Dir]-_),
    replace_splits(FrontPosSplitSubTerms,[Typ,Dir],In,Out),
        % and collect the list of locations of split wave fronts:
    zip(FrontPosSplitSubTerms,PosL,_).

        % split_one_wave_front(Term,VarPosL,SplitTerm): implements steps
        % [2]-[3] of the splitting algorithm described above, where Term
        % is the term to be split (i.e. a ``...'' term picked in step
        % [1]), VarPosL is the position list of {...} terms in Term, and
        % SplitTerm is the result of splitting Term. Backtracks to
        % generate all possible splits of Term.
split_one_wave_front(FrontTerm,VarPosL,TypDir,SplitSubTerm) :-
        % Step [2]:
    label_split(FrontTerm,VarPosL,Labelled),
        % Step [3]:
    Labelled=..[F|Args],
    traverse_split(Args,TypDir,SplitArgs),
    SplitSubTerm=..[F|SplitArgs],
        % Disallow input term to be returned (this can happen if we
        % choose [3][iii][a] at each labelled node):
    SplitSubTerm\=FrontTerm.

        % Pick a wave front which is splittable (ie which has a "depth">=1
        % (depth = max. distance from ``...'' to any {...})
pick_deep_wave_front(Term,FrontPos,VarL,FrontTerm) :-
    wave_fronts(_,FrontList,Term),
    member(FrontPos-VarL/_,FrontList),
    Long=[_,_|_], thereis {Long}:member(Long,VarL),
    exp_at(Term,FrontPos,FrontTerm).

        % label_split(Term,PosList,LabelledTerm)
        % Term is as LabelledTerm, except that all subterms in Term
        % spanning those positions specified in PosList are marked with
        % a '@label@'/1 term.
        % This is step [2] of the algorithm described above.
        %
        % label_split/3 just iterates label_1_var/3 for each element of
        % PosList:
label_split(Term,[],Term).
label_split(Term,[VarPos|VarPosL],Labelled) :-
    reverse(VarPos,VarPosR),
    label_1_var(Term,VarPosR,Term1),
    label_split(Term1,VarPosL,Labelled).
        % label_1_var(Term,Pos,Labelled) labels all positions in Term
        % spanning Pos. Take care not to instantiate any possible
        % meta-variables in Term,  which is why we use functorp/1 a lot,
        % rather than relying on (more efficient) unification.
        % clause 1: termination of descend
        % clause 2: skip terms already labelled (can happen with terms
        %           spanning more than one {...})
        % clause 3: do the real work: descend according to
        %           path-expression, and stick label around the arg as
        %           specified in the path-expression, except when there
        %           already is a label, or when the argument is a {...}
        %           term.
label_1_var(T,[],T).
label_1_var(T,[N|P],T1) :-
    functorp(T,'@label@',1), !,
    T='@label@'(TArg),
    label_1_var(TArg,[N|P],T1).
label_1_var(T,[N|P],T1) :-
    T=..[F|Args],
    partition([F|Args],N,PreNth,Nth,PostNth),
    label_1_var(Nth,P,Nth1),
    (   functorp(Nth1,'@label@',1)    -> LabelNth=Nth1
     ;  functorp(Nth1,'@wave_var@',1) -> LabelNth=Nth1
     ;  LabelNth='@label@'(Nth1)
    ),
    append(PreNth,[LabelNth|PostNth],[F|NewArgs]),
    T1=..[F|NewArgs].

        % Step [3] from the algorithm described above:
        % clause 1: leave variables alone.
        % clause 2: step [3][iii][a]
        % clause 3: step [3][iii][b]
        % clause 4,5: iterate over arg-lists
        % clause 6: step [3][i,ii]
        %
        % The order of clauses 2 and 3 cause splits in large chunks to
        % be computed before small ones. The only real choice between
        % the clauses of this predicate is between 2 and 3, the rest is
        % deterministic. 
traverse_split(Term,_,Term) :- var(Term),!.
traverse_split('@label@'(Term),TypDir,SplitTerm) :-
    Term=..[F|Args],
    traverse_split(Args,TypDir,SplitArgs),
    SplitTerm=..[F|SplitArgs].
traverse_split('@label@'(Term),[Typ,Dir],'@wave_var@'('@wave_front@'(Typ,Dir,SplitTerm))) :-
    unlabel_split(Term,SplitTerm),!.
traverse_split([],_,[]) :- !.
traverse_split([H|T],TypDir,[H1|T1]) :- !, traverse_split(H,TypDir,H1),traverse_split(T,TypDir,T1).
traverse_split(Term,_,Term).

        % Traverse a term and removes anything that smells of '@label@'/1.
unlabel_split(Term,Term) :- var(Term),!.
unlabel_split(Term,Term) :- atomic(Term),!.
unlabel_split([],[]) :- !.
unlabel_split([H|T],[H1|T1]) :- !,unlabel_split(H,H1), unlabel_split(T,T1).
unlabel_split('@label@'(Term),Term1) :- unlabel_split(Term,Term1),!.
unlabel_split(Term,Term1) :-
    Term =..[F|Args],
    unlabel_split(Args,NewArgs),
    Term1=..[F|NewArgs],!.

        % Simply iterate replace/4 over the first argument:
replace_splits([],_,T,T).
replace_splits([(Pos-SplitSubTerm)|PosTermL],[Typ,Dir],Term,SplitTerm) :-
    replace(Pos,'@wave_front@'(Typ,Dir,SplitSubTerm),Term,Split1Term),
    replace_splits(PosTermL,[Typ,Dir],Split1Term,SplitTerm).

        % join_wave_fronts(+Term,?PosL,?JoinTerm) JoinTerm is as Term,
        % but with a number of meeting wave-fronts joined. The joins
        % live in Term as positions specified in PosL.
        %
        % The algorithm is very simple:
        % [1] pick any number of joinable wave fronts (these are places
        %     that look like {``...''} (i.e  places where one wave front
        %     starts at the place where another one ends).
        % [2] perform the joins at places picked in [1].
        %
        % QUESTION: Why is the algorithm for joining so much simpler
        % than that for splitting?
join_wave_fronts(Term,PosL,JoinTerm) :-
    findall(Pos,pick_a_join(Term,Pos),AllPosL),
    PosL=[_|_],
    subseq(AllPosL,PosL,_),
    do_join_wave_fronts(Term,PosL,JoinTerm).
    
        % Find a place where wave fronts can be joined, (these are
        % places that look like {``...''} (i.e places where one wave
        % front starts at the place where another one ends).
pick_a_join(Term,[N|Pos]) :-
    exp_at(Term,[N|Pos],Sub1,Sup1),
    join_comps( Sub1, Sup1, Sub,Typb,Dirb,Sup,_Typp,_Dirp ),
    arg(N,Sup,'@wave_var@'('@wave_front@'(Typb,Dirb,Sub))).
join_comps( Sub1, Sup1, Sub,Typb,Dirb,Sup,Typp,Dirp) :-
    functorp(Sub1,'@wave_front@',3),
    Sub1='@wave_front@'(Typb,Dirb,Sub),
    ( functorp(Sup1,'@wave_front@',3), !,
      Sup1='@wave_front@'(Typp,Dirp,Sup) ;
      Sup1=Sup
    ).


        % iterate the predicate that performs one join:
do_join_wave_fronts(Term,[],Term).
do_join_wave_fronts(Term,[Pos|PosL],JoinTerm) :-
    join_1_wave_front(Term,Pos,Join1Term),
    do_join_wave_fronts(Join1Term,PosL,JoinTerm).    

        % perform one join at the specified position. All we have to do
        % is to remove the {``...''} markers at the specified place. 
join_1_wave_front(Term,[N|Pos],JoinTerm) :-
    exp_at(Term,Pos,Sup1),
    (Sup1='@wave_front@'(Typ,Dir,Sup) orelse Sup1=Sup),
    Sup =.. [F|Args],
    partition([F|Args],N,PreN,Nth,PostN),
    Nth='@wave_var@'('@wave_front@'(Typ,Dir,Sub)),
    append(PreN,[Sub|PostN],[F|NewArgs]),
    NSup =.. [F|NewArgs],
    do_join1_wf( Sup1, Sup, NSup1, NSup ),
%    (Sup1='@wave_front@'(Sup) -> NSup1='@wave_front@'(NSup) ; NSup1=NSup),
    replace(Pos,NSup1,Term,JoinTerm).
do_join1_wf( Sup1, Sup, NSup1, NSup ) :-
    Sup1='@wave_front@'(Typ,Dir,Sup), !, NSup1='@wave_front@'(Typ,Dir,NSup) ; NSup1=NSup.

/*
5.  Code for supporting wave-front rewriting.
*/

%
% This code explicitly uses the internal representation of wave fronts, as
% it cannot be written using wave_fronts/3.
%

      % wave_front_proper( Wave, WaveSansAnnotation )
      % Given a wave-front strip off its outermost annotation
wave_front_proper( '@wave_front@'(_,_,BodyWaveFront),BodyWaveFront).
% Adding by A.Ireland 31/5/91
wave_front_proper( '@wave_front@'(Typ,Dir,BodyWaveFront),Typ,Dir,BodyWaveFront).

      % wave_hole_proper( Hole, HoleSansAnnotation )
      % Given a wave-hole strip off its outermost annotation
wave_hole_proper( '@wave_var@'(Hole), Hole).

/*
 * sink-proper(?T1, ?T2):
 *
 * T1 is identical to T2 except that T1 is enclosed in a sink. 
 * sink-proper/2 can be used to retrieve the contents of a sink 
 * (mode sink-proper(+,-)) or package up a term in a sink 
 * (mode sink-proper(-,+)). Either T1 or T2 must be instantiated.
 */
sink_proper( '@sink@'(BodySink),BodySink).

      % wave_var_terms( Wave, WaveVars )
      % Given a wave return its wave-variables
wave_var_terms( Tm, WvTms ) :-
        findall( WvTm, wave_var_term(Tm, WvTm), WvTms ).
wave_var_term( '@wave_front@'(T,D,X),  '@wave_front@'(T,D,X)) :- !.
wave_var_term( '@wave_var@'(X),  '@wave_var@'(X) ) :- !.
wave_var_term(Tm, X ) :-
        imm_subterms(Tm,STmL,_),
        member( STm, STmL ),
        wave_var_term( STm, X).

    
/* 
 * modify-wave-ann(+WaveSpec, -NewWaveSpec):
 *
 * WaveSpec is a list of wave-front specifications. NewWaveSpec is a
 * a modified version of WaveSpec which takes into account the cancellation
 * of the outermost constructors.
 *
 * Not very elegant. \notnice A normal form for wave-rules where wave-fronts
 * are be maximal split would remove this problem.
 */
modify_wave_ann([],[]).
modify_wave_ann([[_,1]-[[_]]/_|T],TT):-
                modify_wave_ann(T,TT).
modify_wave_ann([[N,1]-[WV]/TypDir|T],[[N,1]-[NewWV]/TypDir|TT]):-
                reverse(WV,[_|L1]),
                reverse(L1,NewWV),
                modify_wave_ann(T,TT).
modify_wave_ann([WF-WVars/TypDir|T],[NewWF-WVars/TypDir|TT]):-
                reverse(WF,[_,N,_|L1]),
                reverse([1,N|L1],NewWF),
                modify_wave_ann(T,TT).

/*
 * mark-potential-waves(+Goal, -NewGoal):
 *
 * Goal and NewGoal are identical formula except that the
 * existential variables in NewGoal are annotated as 
 * potential wave-fronts.
 * NB.  THIS PREDICATE ONLY DEALS WITH EXISTENTIALS IN THE PREFIX!
 */
mark_potential_waves(G,NewG):-
	matrix(Vars,X:Xtype#TX,G),
	mark_potential_waves(X/Dir,TX,NewTX),!,
	matrix(Vars,'@wave_front@'(soft,Dir,X):Xtype#NewTX,NewG).
mark_potential_waves(G,G).

mark_potential_waves(X/Dir,X,'@wave_front@'(soft,Dir,X)).	
mark_potential_waves(_X/_,T,T):- atomic(T).
mark_potential_waves(X/Dir,[H|T],[HH|TT]):-
 	mark_potential_waves(X/Dir,H,HH),
	mark_potential_waves(X/Dir,T,TT).
mark_potential_waves(X/Dir,T,TT):-
	T =.. [F|Args],
	mark_potential_waves(X/Dir,Args,NewArgs),
	TT =.. [F|NewArgs].

/* prepare Thm for processing by add_rewrite_rule/2 */
add_rewrite_rule(Thm) :-
    recorded(theorem,theorem(_,_,Goal,Thm),_),
    matrix(Vars,Matrix,Goal),
    replace_universal_vars(Vars,Matrix,LiftedGoal),
    !,
    add_rewrite_rule(Thm,LiftedGoal).

/* add_rewrite_rule(Thm,Goal) add all the variations of Goal (a
 * rewrite containing prolog variables) as a rewrite to be used during
 * dynamic rippling, under the name Thm.  We insist, since rules will
 * be used in a left-to-right direction, that FV(rhs) \subseteq
 * FV(lhs).  For the same reason, we require that FV(condition)
 * \subseteq FV(lhs).  */
add_rewrite_rule(Thm,LiftedGoal) :-			% implications
    precon_matrix([], C => L => R, LiftedGoal),
    list_to_oyster_conjunction(C,TTC),		% make an Oyster conjunction
    left_and_right_variants(Thm, [TTC,L,R],imp).
add_rewrite_rule(Thm,LiftedGoal) :-			% equality
    precon_matrix([], C => L = R in _, LiftedGoal),
    list_to_oyster_conjunction(C,TTC),		% make an Oyster conjunction
    left_and_right_variants(Thm, [TTC,L,R],equ).
add_rewrite_rule(_Thm,_LiftedGoal).


/* Add left-to-right and right-to-left variants, checking for
 * well-formedness of rewrite-rule.  */
left_and_right_variants(Thm, [C,L,R], Type) :-
    ((proper_rewrite(L,C,R), Dir =.. [Type,left],  Left = L, Right = R);
     (proper_rewrite(R,C,L), Dir =.. [Type,right], Left = R, Right = L)),
    compound(Left),
    writef(' adding rewrite-record for %t...%f',[Thm]),
    uniq_recorda(rewrite,rewrite(Left,Right,C,Dir,Thm),_),
    writef('done\n'), fail.

/* Checks that a rewrite rule is to be used in a sensible direction.  
 * C and R are terms whose (meta-level) free variables are a subset
 * of the (meta-level) free variables of the term L  */
proper_rewrite(Lp,Condsp,Rp) :-
    copy(Lp-Condsp-Rp,L-Conds-R),
    metavarsinterm(L,FVl),
    metavarsinterm(Conds-R,FVr),
    make_ground(FVl-FVr),
    subset(FVr,FVl).



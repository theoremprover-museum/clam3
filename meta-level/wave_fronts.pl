/*
 * This file contains code to deal with wave-rules, wave-fronts etc...
 * The predicates that interface to all this stuff (for use from within
 * methods etc.) all lives in other appropriate files (methods-pred.pl
 * for instance). This file only contains the core code.
 *
 * The file comes in a few pieces:
 * 1. General interface code.
 * 2. Code for abstracting away the implementation of wave fronts.
 * 3. Code for joining and splitting wave fronts.
 * 
 */

/*
 * 1. General interface code.
 * 
 */


replace_subterms([],_,T,T).
replace_subterms([P|Ps],A,T,T2) :-
    replace(P,A,T,T1),
    replace_subterms(Ps,A,T1,T2).

replace_subterms([],T,T).
replace_subterms([P|Ps],T,T2) :-
    replace(P,_,T,T1),
    replace_subterms(Ps,T1,T2).

        % generate all sets of functored subterms of F. 
all_subterms(_,[]).
all_subterms(F,[Pos|PosList]) :-
    exp_at(F,Pos,Sub), Pos\=[],
    exp_at(Sub,[0],Func),
    \+ Func = {},
    \+ exp_at(Sub,_,done),
    replace(Pos,done,F,F1),
    all_subterms(F1,PosList).

        % replace_universal_vars(Vars,Term,NewTerm). Simple loop to
        % replace universally quantified variables. NewTerm is as Term,
        % except that all variables mentioned in Vars (a list with
        % elements Var:Type) will be replaced by meta-(Prolog) variables.
        % Simply iterates replace_all/4, taking care to deal with lists
        % by ourselves, since they are caught as special (namely as
        % introducing local variables) by s/4 which is used by
        % replace_all/4. 
replace_universal_vars(Vars,Term,NewTerm) :-
    untype(Vars,Vs,_), zip(VsNewVs,Vs,_),
    replace_universal_vars_1(VsNewVs,Term,NewTerm).
replace_universal_vars_1(_,Tm,Tm) :- var(Tm),!.
replace_universal_vars_1(VsNewVs,[H|T],[HH|TT]) :- !,
    replace_universal_vars_1(VsNewVs,H,HH),
    replace_universal_vars_1(VsNewVs,T,TT).
replace_universal_vars_1([],In,In).
replace_universal_vars_1([Object-Meta|Vars],In,Out) :- !,
    replace_all(Object,Meta,In,Out1),
    replace_universal_vars_1(Vars,Out1,Out).

/*
 * 2. Code for abstracting away the implementation of wave fronts.
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
 * 3. Code for joining and splitting wave fronts.
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
    partition_([F|Args],N,PreNth,Nth,PostNth),
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
    join_comps( Sub1, Sup1, Sub,Typb,Dirb,Sup,Typp,Dirp ),
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
    partition_([F|Args],N,PreN,Nth,PostN),
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

%*****************************
%*
%*  strip_nested_fronts( +Tm, -StrippedTm )
%*
%*  This functions tidies up ill-formed wave-front annotations.
%*  Wave-fronts nested inside one another, wave-variable annotations
%*  without a surrounding wave-front are dropped.
%*
%**********************

strip_nested_fronts( Tm, _, Tm ) :- (var(Tm);atomic(Tm)),!.
strip_nested_fronts( '@wave_front@'(_,_,'@wave_var@'(Tm)), WState, Rtm ) :-
      strip_nested_fronts(Tm,WState,Rtm),
      !.
% Inserted by A.Ireland
strip_nested_fronts( '@wave_var@'('@wave_front@'(_,_,Tm)), WState, Rtm ) :-
      strip_nested_fronts(Tm,WState,Rtm),
      !.
strip_nested_fronts('@wave_front@'(soft,Dir,Tm),w(_),'@wave_front@'(soft,Dir,Tm)):-!.
strip_nested_fronts(  '@wave_front@'(_,_,Tm), w(WState),RTm ) :- 
      strip_nested_fronts( Tm, w(w(WState)), RTm ),
      !.
strip_nested_fronts( '@wave_front@'(Typ,Dir,Tm), [], '@wave_front@'(Typ,Dir,RTm) ) :-
      strip_nested_fronts( Tm, w([]), RTm ),
      !.
strip_nested_fronts( '@wave_var@'(Tm),w([]),  '@wave_var@'(RTm) ) :-
      strip_nested_fronts(Tm, [], RTm ),
      !.
strip_nested_fronts( '@wave_var@'(Tm), w(WState),  RTm ) :-
      strip_nested_fronts(Tm,WState,RTm),
      !.
strip_nested_fronts( '@wave_var@'(Tm), [], RTm ) :-
      strip_nested_fronts( Tm, [],  RTm ),
      !.
strip_nested_fronts( [H|T], WState, [RH|RT] ) :-
      strip_nested_fronts( H, WState, RH ),
      strip_nested_fronts( T, WState, RT ),
      !.

strip_nested_fronts( Tm, WState, RTm ) :-
      Tm =.. [Func|Args],
      strip_nested_fronts( Args, WState, RArgs ),
      RTm =.. [Func|RArgs].

strip_nested_fronts(Tm,RTm):- strip_nested_fronts( Tm, [], RTm ).

    
/*
6.  Code for supporting wave-front type/direction annotations
*
*   Main predicates:
*
*   wave_typ(Term,Pos,Typ)
*	Returns the type (hard/soft) Typ of the wave at Pos within Term.
*   wave_dir(Term,Pos,Dir)
*	Returns the direction (in/out) Dir of the wave at Pos within Term.
*   all_waves(WaveSpec,Typ,Dir)
*	Succeeds if all waves specified by WaveSpec have type Typ and
*       direction Dir.
*   modify_wave_ann(WaveSpec,NewWaveSpec)
*       Used to modify wave annotation after cancellation has taken place.
*   mark_potential_waves(G,NewG)
*	Marks all existentially quantified variables as potential/soft
*	in G to get NewG.
*
*
*/

%
% 
%

set_wave_dir(T,_,T):-
	(atomic(T);var(T)),!.
set_wave_dir('@wave_front@'(Typ,_,T),Dir,'@wave_front@'(Typ,Dir,T)):-!.
set_wave_dir([H|T],Dir,[HH|TT]):-!,
	set_wave_dir(H,Dir,HH),
	set_wave_dir(T,Dir,TT).
set_wave_dir(T,Dir,TT):-
	T =.. [F|Args],
	set_wave_dir(Args,Dir,NewArgs),
	TT =.. [F|NewArgs].

set_wave_typ(T,_,T):-
	(atomic(T);var(T)),!.
set_wave_typ('@wave_front@'(_,Dir,T),Typ,'@wave_front@'(Typ,Dir,T)):-!.
set_wave_typ([H|T],Typ,[HH|TT]):-!,
	set_wave_typ(H,Typ,HH),
	set_wave_typ(T,Typ,TT).
set_wave_typ(T,Typ,TT):-
	T =.. [F|Args],
	set_wave_typ(Args,Typ,NewArgs),
	TT =.. [F|NewArgs].

wave_dir(Term,Pos,Dir):-
	reverse(Pos,RPos),
	rwave_dir(Term,RPos,Dir).

rwave_dir('@wave_front@'(_,Dir,_),[],Dir).
rwave_dir('@wave_front@'(_,Dir,_):_#_,[],Dir).
rwave_dir(Term,[Pos|PosL],Dir):-
	Term =.. [F|Args],
	nth1(Pos,Args,NTerm),
	rwave_dir(NTerm,PosL,Dir).
	
wave_dir(Term,Pos,Dir,NTerm):-
	reverse(Pos,RPos),
	rwave_dir(Term,RPos,Dir,NTerm).

rwave_dir('@wave_front@'(Typ,Dir,T),[],Dir,'@wave_front@'(Typ,Dir,T)).
rwave_dir('@wave_front@'(Typ,Dir,T),PosL,Dir,'@wave_front@'(Typ,Dir,TT)):-
	rwave_dir(T,PosL,Dir,TT).
rwave_dir('@wave_var@'(T),PosL,Dir,'@wave_var@'(TT)):-
	rwave_dir(T,PosL,Dir,TT).
rwave_dir(Term,[Pos|PosL],Dir,NTerm):-
	Term =.. [F|Args],
	partition_([F|Args],Pos,PrePos,NTerm1,PostPos),
	rwave_dir(NTerm1,PosL,Dir,NTerm2),
	append(PrePos,[NTerm2|PostPos],[NewF|NArgs]),
        NTerm =.. [NewF|NArgs].

	
wave_typ(Term,Pos,Typ):-
	reverse(Pos,RPos),
	rwave_typ(Term,RPos,Typ).

rwave_typ('@wave_front@'(Typ,_,_),[],Typ).
rwave_typ('@wave_front@'(Typ,_,_):_#_,[],Typ).
rwave_typ(Term,[Pos|PosL],Typ):-
	Term =.. [F|Args],
	nth1(Pos,Args,NTerm),
	rwave_typ(NTerm,PosL,Typ).
	
wave_typ(Term,Pos,Typ,NTerm):-
	reverse(Pos,RPos),
	rwave_typ(Term,RPos,Typ,NTerm).

rwave_typ('@wave_front@'(Typ,Dir,T),[],Typ,'@wave_front@'(Typ,Dir,T)).
rwave_typ('@wave_front@'(Typ,Dir,T),PosL,Typ,'@wave_front@'(Typ,Dir,TT)):-
	rwave_typ(T,PosL,Typ,TT).
rwave_typ('@wave_var@'(T),PosL,Typ,'@wave_var@'(TT)):-
	rwave_typ(T,PosL,Typ,TT).
rwave_typ(Term,[Pos|PosL],Typ,NTerm):-
	Term =.. [F|Args],
	partition_([F|Args],Pos,PrePos,NTerm1,PostPos),
	rwave_typ(NTerm1,PosL,Typ,NTerm2),
	append(PrePos,[NTerm2|PostPos],[NewF|NArgs]),
        NTerm =.. [NewF|NArgs].
	
all_waves([],_,_).
all_waves([_-_/[Type,Dir]|Rest],Type,Dir):-
        all_waves(Rest,Type,Dir).

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
 * potential-waves(+Goal, -NewGoal):
 *
 * Goal and NewGoal are identical formula except that the
 * existential variables in NewGoal are annotated as 
 * potential wave-fronts.
 */
potential_waves(V:T=>G,V:T=>GG):-
	potential_waves(G,GG).
potential_waves(V:T#G,VV:T#GG):-
	wave_fronts(V,[[]-[]/[soft,_]],VV),
	replace_all(V,VV,G,G1),
	potential_waves(G1,GG).
potential_waves(C=>G,C=>GG):-
	potential_waves(G,GG).
potential_waves(M,M).
	

mark_potential_waves(G,NewG):-
	matrix(Vars,X:Xtype#TX,G),
	mark_potential_waves(X/Dir,TX,NewTX),!,
	matrix(Vars,'@wave_front@'(soft,Dir,X):Xtype#NewTX,NewG).
mark_potential_waves(G,G).

mark_potential_waves(X/Dir,X,'@wave_front@'(soft,Dir,X)).	
mark_potential_waves(X/_,T,T):- atomic(T).
mark_potential_waves(X/Dir,[H|T],[HH|TT]):-
 	mark_potential_waves(X/Dir,H,HH),
	mark_potential_waves(X/Dir,T,TT).
mark_potential_waves(X/Dir,T,TT):-
	T =.. [F|Args],
	mark_potential_waves(X/Dir,Args,NewArgs),
	TT =.. [F|NewArgs].


wave_var_term(Tm, X ) :-
        imm_subterms(Tm,STmL,_),
        member( STm, STmL ),
        wave_var_term( STm, X).


/******************
*
*    correct_wave_vars( ?Pat, +Inst )
*
*  Unify Pattern Pat against Instance Inst, correcting for the possibility
* that wave-fronts in pattern may have less wave-variables than the
* matching wave-fronts in Inst.
*
******************/

correct_wave_vars( Pat, Inst ) :- var(Pat), Pat = Inst,!.
correct_wave_vars( '@wave_front@'(Typ, Dir, Pat ), '@wave_front@'(Typ, Dir, Inst) ) :-
    !,
    correct_wv( Pat, Inst).
correct_wave_vars( Pat, Inst ) :-
    functor( Inst, F, A ),
    functor( Pat, F, A ),
    Pat =.. [F|Args1],
    Inst =.. [F|Args2],
    correct_wave_varsl( Args1, Args2 ).

correct_wave_varsl( [H1|T1], [H2|T2] ) :-
    correct_wave_vars( H1, H2 ),
    correct_wave_varsl( T1, T2 ).
correct_wave_varsl( [], [] ).

correct_wv(Pat,Inst):- var(Pat),var(Inst),Pat = Inst,!.
% Modified to allow for meta variables in the Inst
correct_wv( Pat, '@wave_var@'(Inst) ) :- \+ var(Inst),Pat = Inst,!.
correct_wv( '@wave_var@'( Inst ), '@wave_var@'( Inst ) ) :- !.
correct_wv( Pat, Inst ) :-
    functor( Inst, F, A ),
    functor( Pat, F, A ),
    Pat =.. [F|Args1],
    Inst =.. [F|Args2],
    correct_wvl( Args1, Args2 ).

correct_wvl( [H1|T1], [H2|T2] ) :-
    correct_wv( H1, H2 ),
    correct_wvl( T1, T2 ).
correct_wvl( [], [] ).

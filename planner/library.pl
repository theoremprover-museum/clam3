/*
 * This file contains a primitive library mechanism which can be used to
 * keep track of dependencies between logical objects such as
 * definitions, theorems, lemma's etc.
 *
 * Main predicates defined in this file are
 *      lib_load/[1;2;3]
 *      lib_save/[1;2]
 *      lib_delete/1
 *      lib_present/1
 *      lib_edit/[1;2]
 *      lib_set/1
 *      lib_tidy/0
 *      needed/2
 */


        % lib_load(+Thing) will load object Thing, plus all other
        % objects needed by Thing which are not already loaded. 
        % 
        % Thing can be:
        % - thm(T): T is a theorem.
        % - lemma(T): T is a lemma which is only needed for technical
        %   reasons, and is not interesting as a thm in its own right.
        %   Thus, if T is both an interesting theorem in its own right
        %   but can also be used as a lemma, it is a thm, not a lemma.
        %   Consequently the only things that should be lemmas are thms
        %   needed for "technical" reasons (ie to beef up arithmetic or so).
        % - wave(T): T is a thm, but is needed in its role as a wave
        %   rule. Consequently, the associated wave/5-record must also
        %   be present
        % - red(T): T is a thm, but can be used as a reduction rule.
        % - synth(T): T is a theorem only used to synthesise a
        %   particular function. In this sense, synths are close to defs.
        % - scheme(T): T is an induction scheme.
        % - def(D): D is a definition. Loading def(D) will also result
        %   in loading all files of the form Dn.eqn, with
        %   n=0,...,9. These are expected to be the recursion equations
        %   for Def.
        % - mthd(M): M is of the form F/A and specifies a method with
        %   functor F of arity A. 
        % - smthd(M): M is of the form F/A and specifies a submethod with
        %   functor F of arity A. 
        % - critic(M): M is of the form F/A and specifies a critic with
        %   functor F of arity A. 
        % 
logical_object(thm(_)).          logical_object(lemma(_)).
logical_object(wave(_)).         logical_object(synth(_)).
logical_object(scheme(_)).       logical_object(def(_)).
logical_object(eqn(_)).          logical_object(red(_)).
logical_object(mthd(_/_)).       logical_object(smthd(_/_)).
logical_object(critic(_/_)).     logical_object(hint(_/_)).
logical_object(comp_rewrite(_)). logical_object(condition_set(_)). 
logical_object(un_defeqn(_)).    logical_object(wave-rules(_)).

/* Following logical objects not currently supported */
% logical_object(templ(_)).       
% logical_object(ndef(_)).        logical_object(rtype(_)).

        % 
        % The corresponding files are expected to be
        %   T.{thm,lemma,synth,scheme,def,mthd,smthd}.
        %
        % Apart from loading the Oyster representation of theorems,
        % defs, etc., we maintain our own storage mechanism which is
        % partly much more efficient than Oysters and partly so that we
        % can cache often re-computed results. This is all done in the
        % recorded database under the keys recursive, wave, theorem and
        % reduction. . 
        % 
        % Dependecies between objects are expected to stored in need/2
        % clauses such as
        %       needs(thm(assm), [def(times)]).
        %       needs(def(times),[def(plus)]).
        % 
        % The real work is done by lib_load/2, which as a second
        % argument takes the directory from which the stuff is to be
        % loaded. If not given it defaults to the value specified by
        % lib_dir/1. 
        %
        % For methods, the arguments are slightly different: second
        % argument is position-in-database (one of
        % {first,last,before(_),after(_)}) or .mthd-file to read methods
        % from. Both arguments can also be given (lib_load/3).
        % The real work for (sub)methods is done by load_mthd in
        % method-db.pl 
        %
        % First clauses only dispatch all cases to their real code:
lib_load([]) :- !.
lib_load([H|T]):- !, lib_load(H),lib_load(T).
lib_load(mthd(M/A))  :- !, load_method(M/A).
lib_load(smthd(M/A)) :- !, load_submethod(M/A).
lib_load(critic(M/A)) :- !, load_critic(M/A).
lib_load(hint(M/A)) :- !, load_hint(M/A).
lib_load(rtype(N)) :- !,lib_dir(LibDir),load_rectype(N,LibDir).
lib_load(templ(N)) :- !,lib_dir(LibDir),load_templs(N,LibDir).
lib_load(Thm) :- lib_dir(LibDir), lib_load(Thm,LibDir).

lib_load([],_):- !.
lib_load([H|T],Arg2) :- !, lib_load(H,Arg2), lib_load(T,Arg2).
lib_load(mthd(M/A),Arg2) :- !, load_method(M/A,Arg2).
lib_load(smthd(M/A),Arg2) :- !, load_submethod(M/A,Arg2).
lib_load(critic(M/A),Arg2) :- !, load_critic(M/A,Arg2).
lib_load(hint(M/A),Arg2) :- !, load_hint(M/A,Arg2).
lib_load(rtype(N),Arg2) :- !,load_rectype(N,Arg2).
lib_load(templ(N),LibDir) :- !,load_templs(N,LibDir).
lib_load(synth(T),Dir) :- !, lib_load(anythm(T,synth),Dir).
lib_load(lemma(T),Dir) :- !, lib_load(anythm(T,lemma),Dir).
lib_load(thm(T),Dir)   :- !, lib_load(anythm(T,thm),Dir).
lib_load(scheme(T),Dir):- !, lib_load(anythm(T,scheme),Dir).


        % "REAL" CODE (for lib_load/2) STARTS HERE:
        % LOADING Function DEFs
        % After loading definition, load all the recursion equations (if
        % any) and also (if applicable) create the recursive/5 record
        % which works as a caching mechansim for recursive/5.
lib_load(def(D),Dir) :- !,
    needs(def(D),Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Dir)),!,
    lib_fname( Dir,D,'synth', SFile),
    ( file_exists(SFile) -> lib_load(synth(D),Dir) ; true ),
    lib_fname( Dir,D,'templ', TFile),
    ( file_exists(TFile) -> lib_load(templ(D),Dir) ; true ),
    writef('loading def(%t)...%f',[D]),
    lib_fname( Dir,D,'def',File),
    create_def(File),
    writef('done\n'),
    lib_load(eqn(D),Dir),
    extend_gaze_graph(D),
    tryto add_recursive_clause(D).

        % LOADING notational DEFs
        % Load up the things the notation depends on, and then the notation
lib_load( ndef(D), Dir ) :-
    needs(ndef(D), Needed ),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Dir)),!,
    writef('loading notational def(%t)...%f',[D]),
    lib_fname(Dir,D,'def',File),
    create_def(File),
    writef('done\n').

        % LOADING EQNs
        % Find out if there are any recursion equations for definition D
        % and call lib_load(anythm(..,eqn)) for each of them. Also, try
        % installing the wave/5 record for those equations to which
        % that applies.
lib_load(eqn(D),Dir) :- !,
    findall(Root,( between(1,20,N),
                  concat_atom([D,N],Root),
                  lib_fname(Dir,Root,'eqn',File),
                  file_exists(File),
                  lib_load(anythm(Root,eqn),Dir)),DRootList),
    add_wave_rules_list(DRootList, _),
    % add_complementary_rewrite_list(DRootList),
    add_func_defeqn_list(DRootList),
    tryto ( DRootList \= []
            % ,add_condition_set(DRootList)
          ),
    findall(Root,( between(1,20,N),
                  concat_atom([D,'_d',N],Root),
                  lib_fname(Dir,Root,'eqn',File),
                  file_exists(File),
                  lib_load(anythm(Root,eqn),Dir)),CRootList),
    add_wave_rules_list(CRootList, _),
    % add_complementary_rewrite_list(CRootList),
    add_func_defeqn_list(CRootList),
    tryto (CRootList \= []
           % ,add_condition_set(CRootList)
          ).


lib_load(eqn(_),_) :- !.
        % LOADING WAVEs
        % Firstly deal with the case where condition sets are
        % specified by the user using the wave([r1,..,rn]) notation.
lib_load(wave(Tlist),Dir) :-
    Tlist = [_|_],
    lib_load_list(thm(Tlist),Dir),
    add_wave_rules_list(Tlist, _).
    % add_complementary_rewrite_list(Tlist),
    % add_condition_set(Tlist).

lib_load(wave-rules(Rn),Dir):-
    lib_fname(Dir,Rn,'wave-rules',File),
    writef('loading wave-rules for %t...%f',[Rn]),
    readfile(File, WaveRules),
    record_wave_rules(WaveRules),
    writef('done\n').
	
record_wave_rules([]).
record_wave_rules([H|T]):-
	uniq_recorda(wave,H,_),
	record_wave_rules(T).
	

        % Secondly deal with the case where a single wave rule
        % is supplied.
        % First load T as a thm and then add the wave/5 record.
lib_load(wave(T),Dir) :- !,
    lib_load(thm(T),Dir),
    add_wave_rules(T, _),
    add_cancel_rule(T).

        % LOADING REDUCTION RULES
        % First load T as a thm and then add the reduction/5 equal or cancel
        % record as appropriate.  Note that we cut to prevent a reduction
        % rule also being recorded as a cancel rule.
lib_load(red(T),Dir) :- !,
    lib_load(thm(T),Dir),
    ( add_reduction_rule(T),! ; 
      add_cancel_rule(T) ; 
      add_equal_rule(T) 
    ).
        % LOADING THMs
        % Deals with synth,lemma,thm,scheme and eqn.
        % Load thing from file and store the theorem/4 record
        % which we use as our own theorem represention (in preference
        % over Oysters one).
lib_load(anythm(Thm,Type),Dir) :- !,
    TypeThm =.. [Type,Thm],
    needs(TypeThm,Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Dir)),!,
    lib_fname(Dir,Thm,Type,File),
    writef('loading %t(%t)...%f',[Type,Thm]),
    load_thm(Thm,File),
    record_thm( Thm, Type ),
    writef('done\n').
        % report error in case of failure.
lib_load(T,_) :- lib_error(T).

        % CODE for lib_load/3 only useful for methods:
lib_load([],_,_).
lib_load([H|T],Where,File) :- lib_load(H,Where,File), lib_load(T,Where,File).
lib_load(mthd(M),Where,File)  :- !, load_method(M,Where,File).
lib_load(smthd(M),Where,File) :- !, load_submethod(M,Where,File).
lib_load(critic(M),Where,File) :- !, load_critic(M,Where,File).
lib_load(hint(M),Where,File) :- !, load_hint(M,Where,File).
lib_load(T,_,_) :- lib_error(T).

record_thm( Thm, Type ) :-
    % Oyster dependent:!
    ctheorem(Thm)=:problem(_==>Goal,_,_,_),
    (Type=eqn
     ->( name(Thm,NameNum),
         append(NameL,[_Num],NameNum),
         name(Name,NameL)
       )
     ; 
     Name=Thm
    ),
    uniq_recorda(theorem,theorem(Name,Type,Goal,Thm),_),
    !.

lib_load_list(thm([]),_).
lib_load_list(thm([H|T]),Dir) :-
    lib_load(thm(H),Dir),
    lib_load_list(thm(T),Dir).
add_wave_rules_list([], _ ).
add_wave_rules_list([H|T], Direction ) :-
    tryto add_wave_rules(H, Direction ),
    add_wave_rules_list(T, Direction ).

add_func_defeqn_list([]).
add_func_defeqn_list([H|T]) :-
    add_func_defeqn(H),
    !,
    add_func_defeqn_list(T).
add_func_defeqn_list([_|T]) :-
    add_func_defeqn_list(T).
add_func_defeqn( H ) :-
    recorded(theorem,theorem(_,_,G,H),_),
    precon_matrix(Vars, C => L = R in _,G),
    decolon_preconds( C, DC ),
    replace_universal_vars(Vars,[L, R, DC ],[QL, QR, QDC ]),
    decolon_preconds( QC, QDC ),
    writef(' adding defeqn-record for %t...%f',[H]),
    uniq_recorda(un_defeqn,
                 un_defeqn(QL,H:QC=>QL:=>QR),_),
    writef('done \n').

extract_condition_set(RuleSet, Cond):-
    findall(LHS-WaveConds-CompConds,
	(member(Rule, RuleSet),
	 wave_rule(Rule, _, [_|_]=>LHS:=>_),
	 extract_conditions(LHS, WaveConds, CompConds)),
         Conds),
    member(Cond, Conds).

extract_conditions(SPat, WaveConds, CompConds):-
        sinks(Pat, _, SPat),
	findall(WC, (wave_rule(_, _, WC1=>SPat:=>_),
                     \+ WC1 = [],
                     sinks(WC, _, WC1)),
                WaveConds),
        wave_fronts(EPat, _, Pat),
	findall(CC, (func_defeqn(EPat, _:CC=>_:=>_),
                    \+ CC = [],
                    \+ member(CC, WaveConds)),
                CompConds),!,
        \+ WaveConds = [].

add_condition_set([]).
add_condition_set(Tlist):-
    \+ (member(Rn, Tlist), wave_rule(Rn, _, [_|_]=>_:=>_)),!.
add_condition_set(Tlist):-
    writef(' adding condition-set-record for %t...%f', [Tlist]),
    extract_condition_set(Tlist, Pat-WaveCond-CompCond),
    \+ condition_set(Pat, WaveCond, CompCond),
    writef('.'),
    uniq_recorda(condition_set,condition_set(Pat, WaveCond, CompCond), _),
    fail.
add_condition_set(_):-
    writef('done\n').

add_sym_eval_set( Exp, Conds, Names ) :-
    % For the moment we exclude case-analysis that might
    % always be applicable
    wave_fronts( NWExp, [_|_], Exp ),
    \+ ( member( N, Names ),
	 \+ ( func_defeqn(_,N:_) ;
	      reduction_rule(_,N:_,_) ;
	      cancel_rule( _,N:_)
            )
       ),
    writef(' adding sym-eval-set-record for %t...%f', [Names]),
    uniq_recorda(sym_eval_set,sym_eval_set(NWExp,Conds),_),
    writef('done\n'),
    !.
add_sym_eval_set( _, _, _ ).

lib_tidy :-
    recorded(wave,_,R),
    erase(R),
    fail.
lib_tidy :-
    recorded(comp_rewrite,_,R),
    erase(R),
    fail.
lib_tidy :-
    recorded(condition_set,_,R),
    erase(R),
    fail.
lib_tidy :-
    erasereln( induction_lemma ),
    erasereln( precond_lemma ),
    erasereln( str_case_lemma ),
    erasereln( lemma ),
    erasereln( shell ),
    erasereln( template ),
    fail.
lib_tidy.

        % lib_save(Thing, Dir) saves Thing in directory Dir in files
        % with the appropriate suffix.
        %
        % lib_save(Thing) is as lib_save/2, with Dir defaulting to the
        % current dir:
lib_save(Thing) :- saving_dir(D),lib_save(Thing, D).
lib_save(thm(T), Dir) :- !, lib_save(anythm(T,thm),Dir).
lib_save(eqn(T), Dir) :- !, lib_save(anythm(T,eqn),Dir).
lib_save(lemma(T), Dir) :- !, lib_save(anythm(T,lemma),Dir).
lib_save(scheme(T), Dir) :- !, lib_save(anythm(T,scheme),Dir).
lib_save(synth(T), Dir) :- !, lib_save(anythm(T,synth),Dir).
lib_save(wave(T), Dir) :- !, lib_save(anythm(T,thm),Dir).
lib_save(red(T), Dir) :- !, lib_save(anythm(T,thm),Dir).
        % lib_save anythm in appropriate file
lib_save(anythm(T,Type),Dir) :- !,
    lib_fname(Dir,T,Type,File),
    writef('saving %t(%t)...%f',[Type,T]),
    save_thm(T,File),
    writef('done\n').
lib_save(wave-rules(Rn),Dir):-
    lib_fname(Dir,Rn,'wave-rules',File),
    writef('saving wave-rules(%t)...%f',[Rn]),
    findall(wave(Rn, Rule, TypDir), wave_rule(Rn, TypDir, Rule), Rules),
    tell(File),writeq(Rules),write('.'),nl,told,
    fail.
lib_save(wave-rules(Rn),Dir):-
    writef('done\n').
        % For saving definitions we first save the def (easy), and then
        % save all the eqns for that def.
lib_save(def(D),Dir) :- !,
    definition(D/_<==>_), 
    lib_fname(Dir,D,'def',File),
    writef('saving def(%t)...%f',[D]),
    save_def(D,File),
    writef('done\n'),
    ( lib_present( synth(D) ) -> lib_save( synth(D), Dir ) ; true ),
    ( lib_present( templ(D) ) -> lib_save( templ(D), Dir ) ; true ),
    lib_save(eqn(D),Dir).

        % Saving notational def's - just save it!
lib_save(ndef(D),Dir) :- !,
    definition(D/_<==>_), 
    lib_fname( Dir,D,'def',File),
    writef('saving def(%t)...%f',[D]),
    save_def(D,File),
    writef('done\n'),
    ( lib_present( synth(D) ) -> lib_save( synth(D) ) ; true ).

        % Saving eqns: Pick up all thms that could be eqns for this
        % Def, and save em.
lib_save(eqn(D),Dir) :- !, 
    forall {Eqn\( between(1,20,N),
                  ( concat_atom([D,N], Eqn); concat_atom([D,'_d',N],Eqn) ),
                  ctheorem(Eqn) =: _
%                  ) 
                )
           } : 
                 lib_save(anythm(Eqn,eqn),Dir).
lib_save(mthd(-),_)  :- !,writef('CLaM ERROR: Cannot save methods (yet)\n').
lib_save(smthd(_),_) :- !,writef('CLaM ERROR: Cannot save submethods (yet)\n').
lib_save(critic(_),_) :- !,writef('CLaM ERROR: Cannot save critics (yet)\n').
lib_save(hint(-),_)  :- !,writef('CLaM ERROR: Cannot save hints (yet)\n').
lib_save(rtype(N),Dir) :- !,save_rectype(N,Dir).
lib_save(templ(N),Dir) :- !,save_templs(N,Dir).
        % Iterate over lists:
lib_save([],_) :- !.
lib_save([H|T],Dir) :- !, lib_save(H,Dir), lib_save(T,Dir).
        %
lib_save(T,_) :- lib_error(T).

        % lib_present(?Object) succeeds if Object is present in the
        % current environment.
        % Can be used to test for presence, or to generate the entire
        % contents of the currently loaded library if you feel like it.
        % The order of the clauses below is significant: Defs create
        % eqns and eqns create thms, so the order is def;eqn;thm. This
        % is so that lib_delete(-) can use this predicate to generate
        % the library in a decent order for deleting things. 
lib_present(def(T)) :- definition(T/_<==>_).
lib_present(eqn(T)) :- recorded(theorem,theorem(_,eqn,_,T),_).
lib_present(wave(T)) :- recorded(wave, wave(T,_,_),_).
lib_present(red(T)) :- recorded(reduction,reduction(_,T:_,_),_);
                       recorded(equal,equal(_,T:_),_);
                       recorded(cancel,cancel(_,T:_),_).
lib_present(thm(T)) :- recorded(theorem,theorem(T,thm,_,_),_).
lib_present(lemma(T)) :- recorded(theorem,theorem(T,lemma,_,_),_).
lib_present(synth(T)) :- recorded(theorem,theorem(T,synth,_,_),_).
lib_present(scheme(T)) :- recorded(theorem,theorem(T,scheme,_,_),_).
lib_present(comp_rewrite(T)) :- recorded(comp_rewrite,comp_rewrite(_,_,T:_),_).
lib_present(mthd(M)) :- list_methods(L), remove_dups(L,L1),member(M,L1).
lib_present(smthd(M)) :- list_submethods(L), remove_dups(L,L1),member(M,L1).
lib_present(critic(M)) :- list_critics(L), remove_dups(L,L1),member(M,L1).
lib_present(hint(M)) :- list_hints(L), remove_dups(L,L1),member(M,L1).
lib_present(un_defeqn(T)) :- recorded(un_defeqn,un_defeqn(_,T:_),_).
/* 
 * The following two clauses are required to integrate Clam 
 * with Andrew Stevens shell mechanism.
 *
 * lib_present(rtype(N)) :- tuple(shell,[M|_]),def_appl(N,_,M),!.
 * lib_present(templ(N)) :- tuple(template,[N|_]),!.
 */
lib_present(T) :-
    \+ var(T), T\==[], \+ functorp(T,.,2),\+ logical_object(T), lib_error(T).

        % lib_present prints out all objects currently in the library.
lib_present :- lib_present(O), write(O), nl, fail.
lib_present.

        % lib_delete(?Object) removes Object from the current
        % environment. Fails if Object is not present in the current
        % environment.
        % First clause makes that we can use mode lib_delete(-), which,
        % on backtracking, will delete the whole library.
lib_delete(Object) :- var(Object), !, lib_present(Object),lib_delete(Object).
lib_delete(Object) :-
    \+ var(Object),
    \+ functorp(Object,anythm,2), Object\==[], \+ functorp(Object,.,2),
    \+ logical_object(Object),
    !,lib_error(Object).
lib_delete(Object) :-
    logical_object(Object),
    \+ (Object=anythm(_,_); lib_present(Object)),
    writef('CLaM WARNING: %t not present, so cannot be deleted\n',[Object]),
    !,fail.
        % Map most cases into anythm:
lib_delete(thm(T)) :- lib_delete(anythm(T,thm)).
lib_delete(lemma(T)) :- lib_delete(anythm(T,lemma)).
lib_delete(wave(T)) :- lib_delete(anythm(T,wave)).
lib_delete(comp_rewrite(T)) :- lib_delete(anythm(T,comp_rewrite)).
lib_delete(red(T)) :- lib_delete(anythm(T,red)).
lib_delete(eqn(T)) :- lib_delete(anythm(T,eqn)),
                      lib_delete(anythm(T,wave)).
lib_delete(synth(T)) :- lib_delete(anythm(T,synth)).
lib_delete(scheme(T)) :- lib_delete(anythm(T,scheme)).
lib_delete(un_defeqn(T)) :- lib_delete(anythm(T,un_defeqn)).
        % anythm case does most work: delete theorem-, reduction-, wave- and
        % recursive-records (if any), and delete thm itself.
lib_delete(anythm(T,Type)) :-
    findall(Ref,
            (recorded(theorem,theorem(_,_,_,T),Ref),
             writef('deleting theorem record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(wave,wave(T,_,_),Ref),
             writef('deleting wave record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(equal,equal(_,T:_),Ref),
             writef('deleting equal record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(cancel,cancel(_,T:_),Ref),
             writef('deleting cancel record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(un_defeqn,un_defeqn(_,T:_),Ref),
             writef('deleting func_defeqn record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(reduction,reduction(_,T:_,_),Ref),
             writef('deleting reduction record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    findall(Ref,
            (recorded(comp_rewrite,
                      comp_rewrite(_,_,T:_),Ref),
             writef('deleting complementary_rewrite record for %t...%f',[T]),
             erase(Ref), writef('done\n')
            ),_),
    writef('deleting %t(%t)...%f',[Type,T]),
    ctheorem(T) := _ , writef('done\n').
        % For def's, for recursive definitions, we delete recursive
        % record, pick up all the equations and delete them, and finally
        % we delete def itself.  
lib_delete(def(D)) :-
    definition(D/N<==>_), functor(Skel,D,N),
    tryto (recorded(recursive,recursive(Skel,_,_,BaseL,StepL,_),Ref),
           writef('deleting recursive record for %t...%f',[D]),
           erase(Ref), writef('done\n'),
           findall(Step, (member(Step:_, StepL), lib_delete(eqn(Step))),_),
           findall(Base, (member(Base:_, BaseL), lib_delete(eqn(Base))),_)
          ),!,
    tryto lib_delete(synth(D)),
/*
 *  templ are generated by the shell mechanism which
 *  is currently not supported by Clam.v1.5.
 *
 *  tryto lib_delete(templ(D)),
 */
    writef('deleting def(%t)...%f',[D]),
    erase_def(D),writef('done\n').
        % For (sub)methods we map into the code that handles the
        % (sub)method databases.
        % The calls to lib_present/1 are strictly speaking unnecessary
        % (since we already tested for presence of mthd(M/A) at the top
        % of lib_delete), but it serves to instantiate M/A properly if
        % lib_delete was called with a var argument.
lib_delete(mthd(M/A)) :-
    lib_present(mthd(M/A)),
    writef('deleting %t...%f',[mthd(M/A)]),
    delete_method(M/A),
    writef('done\n').
lib_delete(smthd(M/A)) :-
    lib_present(smthd(M/A)),
    writef('deleting %t...%f',[smthd(M/A)]),
    delete_submethod(M/A),
    writef('done\n').
lib_delete(critic(M/A)) :-
    lib_present(critic(M/A)),
    writef('deleting %t...%f',[critic(M/A)]),
    delete_critic(M/A),
    writef('done\n').
lib_delete(hint(M/A)) :-
    lib_present(hint(M/A)),
    writef('deleting %t...%f',[hint(M/A)]),
    delete_hint(M/A),
    writef('done\n').
lib_delete(templ(D)) :-
    erasetuple(template,[D|_]).
        % iterative version:

lib_delete([]).
lib_delete([H|T]) :- lib_delete(H), lib_delete(T).

        % lib_delete deletes all objects in the current library.
lib_delete :- lib_delete(_), fail.
lib_delete.

        % lib_set/1 can set some global parameters. Currently only the
        % default directory for library-loading and the editor called by
        % lib_edit. 
lib_set(dir(D)) :- !,
    writef('Setting %t...%f',[dir(D)]),
    remove_pred(lib_dir,1), assert(lib_dir(D)),
    writef('done\n').
lib_set(sdir(D)) :- !,
    writef('Setting %t...%f',[sdir(D)]),
    remove_pred(saving_dir,1),
    assert(saving_dir(D)).
lib_set(editor(E)) :- !,
    writef('Setting %t...%f',[edit(E)]),
    remove_pred(lib_editor,1), assert(lib_editor(E)),
    writef('done\n').
lib_set(_) :-
    writef('CLaM ERROR: Can (currently) only set dir(D) or editor(E)\n'),
    !,fail.

        % lib_edit(+Mthd) will edit Mthd (which is a (sub)method
        % specification of the form mthd(M/N) or smthd(M/N)). After
        % editing, Mthd will be loaded.
        % Optional second argument specifies directory where Mthd is to
        % be found, defaulting to the library directory.
        %
        % lib_edit/0 will edit most recently edited (sub)method.
:- dynamic lib_editor/1.
lib_edit(Mthd) :- lib_dir(Dir), lib_edit(Mthd,Dir).
lib_edit(Mthd,Dir) :- clause(lib_editor(Edit),_),!,lib_edit(Mthd,Dir,Edit).
lib_edit(Mthd,Dir) :- 
    (environ('VISUAL', Edit)
     orelse environ('EDITOR', Edit)
     orelse Edit=vi
    ),
    assert(lib_editor(Edit)),
    lib_edit(Mthd,Dir).
lib_edit(Mthd,Dir,Edit) :-
    Mthd =.. [Type,M/_], member(Type,[mthd,smthd,critic]),
    (recorded(lib_edit,_,Ref)->erase(Ref);true),
    recorda(lib_edit,(Mthd,Dir),_),
    concat_atom([Edit,' ',Dir,'/',M,'.',Type],Command),
    unix(shell(Command)),!,
    lib_load(Mthd,Dir).
lib_edit(_,_,_) :-
    writef('CLaM ERROR: Can (currently) only edit mthd(M/N), smthd(M/N) or critic(M/N)\n'),
    !,fail.
lib_edit :-
    recorded(lib_edit,(Mthd,Dir),_),!,lib_edit(Mthd,Dir).
lib_edit :-
    writef('CLaM ERROR: No previously edited object\n'),!,fail.

        % Try to give decent error messages to user:
lib_error(AnyThing) :-
    \+ logical_object(AnyThing),
    findall(O,logical_object(O),Os), numbervars(Os,0,_),
    writef('CLaM ERROR: Illegal specification of logical object: %t.\n',
                        [AnyThing]),
    writef('            Should be one of:\n'),prlist(Os),fail.

        % transitive closure of the needs/2 relation. Can be used
        % both ways round! For example:
        %   needed(thm(t1),def(D)) finds all definitions needed for
        %   theorem t1, and
        %   needed(thm(T),def(d1)) finds all theorems that need
        %   definition d1. 

needed(Needer,Needed) :-
    needs(Needer,N),
    member(Needed,N).
needed(Needer,Needed) :-
    needs(Needer,N),
    member(N1,N),
    needed(N1,Needed).

delete_lemmas :-
    recorded(lemma_cnt,N,Ref),
    erase(Ref),
    delete_lemmas(1,N),
    uniq_recorda(lemma_cnt,1,_).

delete_lemmas(N,Max):-
    N < Max,
    name(N, StrN),
    append([108,101,109,109,97], StrN, StrName),
    name(Name, StrName),
    (lib_delete(thm(Name));true),
    delete_goaltree(Name),
    M is N+1,
    delete_lemmas(M, Max).
delete_lemmas(_, _).

delete_hovs(Name):-
    recorded(hov_cnt,N,_),
    delete_hovs(1,N),
    uniq_recorda(hov_cnt,1,_),
    uniq_recorda(Name, environment([]), _).

delete_hovs(N,Max):-
    N < Max,
    name(N, StrN),
    append([104,111,118], StrN, StrName),
    name(Name, StrName),
    (retract(type(clam,Name,_));true),
    M is N+1,
    delete_hovs(M, Max).
delete_hovs(_, _).

        % uniq_recorda/3 is like recorda/3, except that it has
        % specialised knowledge about what kind of duplicate information
        % should be avoided in the various databases. If it spots a
        % potential duplicate, it first removes the duplicate and calls
        % itself again.
        % This means that we don't have to worry about duplicates in all
        % the places where we do record's, but we can leave it to this
        % predicate to take care of avoiding duplication.
        % 
        % Since this predicate uses unification to match existing
        % records and new records, it can happen (and does happen) that
        % it gets caught out by Prolog's lack of occur's check when
        % records contain unbound variables.
        % In those cases we therefore make the existing item ground before
        % unification (and then of course have to use double negation to
        % avoid variables in the new record to get bound).

uniq_recorda(theorem, theorem(Name,Type,_,Thm),_) :-
    recorded(theorem, theorem(Name,Type,_,Thm),OldRef),
    erase(OldRef),
    fail.
uniq_recorda(reduction, reduction(_,RuleName:_,_),_) :-
    recorded(reduction, reduction(_,RuleName:_,_),OldRef),
    erase(OldRef),
    fail.
uniq_recorda(comp_rewrite, comp_rewrite(Pat,_,RuleName:_),_) :-
    recorded(comp_rewrite, comp_rewrite(ExistingPat,_,RuleName:_),OldRef),
    % ocunifiable(ExistingPat, Pat),
    matches(ExistingPat, Pat),
    erase(OldRef),
    fail.
uniq_recorda(un_defeqn, un_defeqn(Pat, RuleName:_),_) :-
    recorded(un_defeqn, un_defeqn(ExistingPat, RuleName:_),OldRef),
    % ocunifiable(ExistingPat, Pat),
    matches(ExistingPat, Pat),
    erase(OldRef),
    fail.
uniq_recorda(condition_set, condition_set(Pat, _, _), _) :-
    recorded(condition_set, condition_set(ExistingPat, _, _), OldRef),
    % ocunifiable(ExistingPat, Pat),
    matches(ExistingPat, Pat),
    erase(OldRef),
    fail.
uniq_recorda(wave,wave(RuleName, _ => LHS :=> _, _) ,_) :-
    recorded(wave,wave(RuleName, _ => ExistingLHS :=> _, _), OldRef),
    % ocunifiable(ExistingLHS, LHS),
    matches(ExistingLHS, LHS),
    erase(OldRef),
    fail.
uniq_recorda(recursive,recursive(Skel_Term,N,_,_,_,_),_) :-
    recorded(recursive,recursive(Existing_Skel_Term,N,_,_,_,_),OldRef),
    % ocunifiable( Existing_Skel_Term, Skel_Term ),
    matches( Existing_Skel_Term, Skel_Term ),
    erase(OldRef),
    fail.
uniq_recorda( method, _, _) :-
      recorded( method, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( submethod, _, _ ) :-
      recorded( submethod, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( critic, _, _ ) :-
      recorded( critic, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( hint, _, _ ) :-
      recorded( hint, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( lemma_cnt, _, _ ) :-
      recorded( lemma_cnt, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( hov_cnt, _, _ ) :-
      recorded( hov_cnt, _, OldRef ),
      erase(OldRef),
      fail.
uniq_recorda( current_goaltree, _, _ ) :-
     recorded( current_goaltree, _, OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, method(A,_ ), _ ) :-
     recorded( Index, method(A,_), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, submethod(A, _ ), _ ) :-
     recorded( Index, submethod(A,_), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, hint(A, _ ), _ ) :-
     recorded( Index, hint(A,_), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, critic(A, _ ), _ ) :-
     recorded( Index, critic(A,_), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, plans(_, _), _ ) :-
     recorded( Index, plans(_, _), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, environment(_), _ ) :-
     recorded( Index, environment(_), OldRef ),
     erase(OldRef),
     fail.
uniq_recorda( Index, subst(_), _ ) :-
     recorded( Index, subst(_), OldRef ),
     erase(OldRef),
     fail.

        % base clause does the real work (ie. if no duplicate is found,
        % possibly after duplicates have removed):
uniq_recorda(Index,Term,Ref) :- recorda(Index,Term,Ref).

% z version for opposite ordering

uniq_recordz(wave,wave(RuleName,Rule,Type_and_Dir,N,T,F),_) :-
    recorded(wave,wave(RuleName,ExistingRule,Type_and_Dir,N,T,F),OldRef),
    % ocunifiable( ExistingRule, Rule ),
    matches( ExistingRule, Rule ),
    erase(OldRef),
    fail.
uniq_recordz(Index,Term,Ref) :- recordz(Index,Term,Ref).


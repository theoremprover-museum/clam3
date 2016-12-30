  :- dynamic foo/0.
  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   
%  File:  Specials.pl

%  This file contains the code for all the special goals currently
%  implemented.  These functions are defined by the describe commands. 

:- dynamic printtypes/0, freezetypes/0, projfirst/0, tvw/0, hp_trace_options/1.

%  special_goal(Modules,Uvars, Goal,Newdpairs) used to solve the defined predicates.
%  Newdpairs indicates an additional set of disagreement pairs that may have
%  to be unified.

%  First a predicate that provides information about the defined predicates.

  special_goal(_,_,cv(help,o,c),[]) :-
    write_text([
'The following special predicates are provided with LP',
'  Input-Output:     read, write, writesans, nl, see, tell, seen, told',
'  Module related:   paths, add_path, lp_remove_path, show_paths, load, unload,',
'                    reload, use, unuse, write_module',
'  Meta Level:       !, fail, not, is, iss',
'  F-F Constraints:  clean_ff',
'  Miscellaneous:    =, listing, recon, bye, halt, stop, break, fp',
'                    statistics, trace, untrace, switch, system',
'To get more information about any of these which are not infix, use the goal',
'     describe <predicate-name>',
'To get help on the infix predicates "=" "is", and "iss" use the commands',
'describe_=, describe_is, and describe_iss goals.',
'  ']).


% For more information about any one predicate.
  special_goal(_,_,cv(describe,A ---> o,c) ^ cv(Pred,A,c), []) :- 
                            !, describe_text(Pred,Text), write_text(Text).

  special_goal(_,_,cv('describe_=',o,c), []) :- 
                            !, describe_text(=,Text), write_text(Text).

  special_goal(_,_,cv(describe_is,o,c), []) :- 
                            !, describe_text(is,Text), write_text(Text).

  special_goal(_,_,cv(describe_iss,o,c), []) :- 
                            !, describe_text(iss,Text), write_text(Text).


% Some of the logical operations available in LP

   special_goal(_,_,cv(true,o,c),[]) :- !.

   special_goal(_,_,cv(fail,o,c),[]) :- !, fail.

   special_goal(_,Uvars,cv('=',A ---> A ---> o,c)^T1^T2,[[A1,A2]]) :- !,
	huet_normal(A1,hn(Uvars,T1,[])),
	huet_normal(A2,hn(Uvars,T2,[])).

% is and iss. These call for evaluation.
   special_goal(_,_,cv(is,(A ---> B) ---> (A ---> B) ---> o,c) ^ _ ^ _,_) :-
                  !, write('Cannot evaluate functional object.'),nl,fail.

   special_goal(_,Uvars,cv(is,A ---> A ---> o,c) ^ T ^ T1,[[B,B2]]) :-
	eval([],T1,T2),!,
	huet_normal(B,hn(Uvars,T,[])),
	huet_normal(B2,hn(Uvars,T2,[])).


   special_goal(Modules,Uvars,cv(is,A ---> A ---> o,c) ^ T ^ T1,_) :-
        write('Bad goal being evaluated'), nl, write_term_lp(T1,main), !, fail.

   special_goal(Modules,Uvars,cv(iss,(Ty ---> o) ---> (Ty ---> o) ---> o,c)^T^T1,[[A,A2]]) :-
	eval_bag(Modules,Ty,T1,T2),!,
	huet_normal(A,hn(Uvars,T,[])),
	huet_normal(A2,hn(Uvars,T2,[])).


% Hook onto the functional programming component
   special_goal(_,_,cv(fp, o, c),[]) :- fp.

% Saving the state of the system.
   special_goal(_,_,cv(save,o,c),[]) :-
                           !, save_program('lp.save',lp), sign_on,nl.

   save_lp :- save_lp('lp.save').
   save_lp(File) :- save(File), sign_on, lp.
   sign_on :- sign(S), write(S),nl,fail.
   sign_on.


% for interacting with modules
   special_goal(_,_,cv(paths,A ---> o,c) ^ cv(File,A,c),[]) :-
		[File], !.
   special_goal(_,_,cv(add_path,A ---> o,c) ^ cv(Path,A,c),[]) :-
		assert(path_name(Path)), !.
   special_goal(_,_,cv(lp_remove_path,A ---> o,c) ^ cv(Path,A,c),[]) :-
		(retract(path_name(Path)), ! ; 
	 write('No such path is known currently'), nl),
		!.
   special_goal(_,_,cv(show_paths,o,c),[]) :-
	!, 
        (bagof(Path, path_name(Path), Paths), !, 
         write('The following directories are currently searched for modules'),
               nl, write_paths(Paths) ;
         write('No directories are currently searched for modules'), nl).


   special_goal(_,_,cv(use,A ---> o,c) ^ cv(Module,A,c),[]) :-
        !,
        load_modules([Module]),
        add_to_importlist(main,[Module]), add_mlinks(main,[Module]).

   special_goal(_,_,cv(unuse,A ---> o,c) ^ cv(Module,A,c),[]) :-
        !,
        delete_from_importlist(main,[Module]), delete_mlinks(main,[Module]).

   special_goal(_,_,cv(load,A ---> o,c) ^ cv(Mname,A,c),[]) :- 
                                               !, load_modules([Mname]).

   special_goal(_,_,cv(reload,A ---> o,c) ^ cv(Mname,A,c),[]) :- 
                         !, unload_module(Mname), load_modules([Mname]).

   special_goal(_,_,cv(unload,A ---> o,c) ^ cv(Mname,A,c),[]) :- 
                                                !, unload_module(Mname).


% Predicates for examining current definitions
   special_goal(Mods,_,cv(listing, Ty ---> o,c)^cv(Pred,Ty,c),[]) :-
	   (clause_instance(Mods,_,_,cv(Pred,Ty,c),Clause), 
					hp_listing(Mods,cv(Pred,Ty,c)), nl ;
	    write(' No clauses known for '), write(Pred),
					write(' in modules '), write(Mods), nl),
	   !.

   hp_listing(Mods,Pred) :-
	clause_instance(Mods,_,Source,Pred,Clause), 
	nl, write('   '), write_term_lp(Clause,Source), write('.'), nl, fail.
   hp_listing(_,_) :- !.


   special_goal(_,_,cv(write_module,A ---> o,c) ^ cv(Mname,A,c),[]) :- 
                                                 !, write_module(Mname).


% Input-output predicates
   special_goal(_,_,cv(write,A ---> o,c) ^ Term,[]) :-
                            !, write_term_lp(Term,main).

   special_goal(_,_,cv(writesans,string ---> o,c)^cv(Str,string,c),[]) :-  
				!, write(Str).

   special_goal(_,_,cv(nl,o,c),[]) :-  nl,!.

   special_goal(_,_,cv(tell,Ty ---> o, c) ^ cv(File,Ty,c),[]) :- tell(File),!.

   special_goal(_,_,cv(told, o, c),[]) :- told,!.

   special_goal(_,Uvars,cv(read,A ---> o,c) ^ Term,[[Abst_t,Abst_term]]) :-
      !, write(' ?- '), read_line(Line),
      parse_term(main,'.',TTerm,[],[],[],_,[],_,[],_,Line,Err,Line,[]),
      Err = false, TTerm = [T,A],
      huet_normal(Abst_t,hn(Uvars,T,[])),
      huet_normal(Abst_term,hn(Uvars,Term,[])).


   special_goal(_,_,cv(see,Ty ---> o,c) ^ cv(File,Ty,c),[]) :- !, see(File).

   special_goal(_,_,cv(seen,Ty ---> o,c), []) :- !, seen.


% Exiting the system. HALT or BYE get you out of lambda Prolog and
% Prolog.  STOP gets you to the Prolog interpreter.  BREAK calls Prolog
% recursively.  Exit with ^D.

   special_goal(_,_,cv(halt,o,c),[]) :- halt.

   special_goal(_,_,cv(bye,o,c),[]) :- halt.

   special_goal(_,_,cv(stop,o,c),[]) :- abort.

   special_goal(_,_,cv(break,o,c),[]) :- break.


% Tracing the lambda Prolog interpreter. The argument may be one of CLAUSE, GOAL,
% INTERP, UNIFIER, and this indicates the particular tracing option.  Code for
% hp_trace is at end of file.  (hp_trace is historical: lambda Prolog was once
% called Higher-Order Prolog.
   special_goal(_,_,cv(trace,opt ---> o,c) ^ cv(Opt,opt,c),[]) :-
                (var(Opt), !, runtime_error(trace, var) ;
                 \+ lp_member(Opt,[clause,goal,interp,unifier,allopts]),
                              runtime_error(trace, option, Opt) ;
                 hp_trace(Opt),  hp_trace_options(L),
		   write('The following tracing options are on currently: '),
			nl, writeblanks(2), write(L),nl,!).

   special_goal(_,_,cv(untrace,opt ---> o,c) ^ cv(Opt,opt,c),[]) :-
                (var(Opt), !, runtime_error(trace, var) ;
                 \+ lp_member(Opt,[clause,goal,interp,unifier,allopts]),
                              runtime_error(trace, option, Opt) ;
		 hp_untrace(Opt), hp_trace_options(L),
		   (L = [],
		     write('   All tracing options are off currently.') ;
		    write('The following tracing options are on currently: '),
			nl, writeblanks(2), write(L)),
		    nl,!).



% Miscellaneous predicates.
   special_goal(_,_,cv(statistics,o,c),[]) :- statistics.

   special_goal(_,_,cv(switch,swopt ---> onoff ---> o,c) ^ X ^ Y,[]) :- 
	(X = cv(Z,A,c),
	   (Z = printtypes ; Z = freezetypes ; Z = projfirst ; Z = tvw ),
	       (Y == cv(on,onoff,c), SetOption =.. [Z,on], call(SetOption) ;
	        Y == cv(off,onoff,c), SetOption =.. [Z,off], call(SetOption) ;
	        write('    Invalid switch value for option '), write(Z), nl) ;
	 write('    Invalid switch option encountered.'), nl), 
	!.

   printtypes(Val) :- 
       (Val = on, (printtypes ; assert(printtypes)) ;
	Val = off, (retract(printtypes) ; true)), !.

   freezetypes(Val) :-
       (Val = on, (freezetypes ; assert(freezetypes)) ;
	Val = off, (retract(freezetypes) ; true)), !.

   projfirst(Val) :-
       (Val = on, (projfirst ; assert(projfirst)) ;
	Val = off, (retract(projfirst) ; true)), !.

   tvw(Val) :-
       (Val = on, (tvw ; assert(tvw)) ;
	Val = off, (retract(tvw) ; true)), !.

   tvw.

   special_goal(_,_,cv(internal,A ---> o,c) ^ Term,[]) :-
                                             !, write(Term).
   special_goal(_,_,cv(recon,Ty ---> o,c) ^ cv(File,Ty,c),[]) :- 
	!, 
	(stringtype(Ty1), Ty == Ty1, Fullname = File ; 
	 append_names(File,'.pro',FullName)),
	!, [FullName].


   special_goal(_,_,cv(system,string ---> o,c)^cv(Str,string,c),[]) :- 
        name(Str,List),
	system(List),nl.


% This goal is not too clean.  The program for which you are getting the
% definition should not contain type variables in it clauses.

   special_goal(Modules,Uvars,cv(definition,A ---> o ---> o,c) ^ Pred ^ Clist,
                [[Alist,A1]]) :-
        collect_clause(Pred,Modules,C),
	list_and_lp_conj(C,C1),
	huet_normal(Alist,hn(Uvars,Clist,[])),
	huet_normal(A1,hn(Uvars,C1,[])).

   collect_clause(Pred,Mods,Cclist) :-
        bagof(Clause,Mod^( clause_instance(Mods,_,_,Pred,Clause)),Clist),
        universal_closure_list(Clist,Cclist).

   list_and_lp_conj([X],X).
   list_and_lp_conj([X|L],cv(',',o ---> o ---> o,c) ^ X ^ K) :-
                                            list_and_lp_conj(L,K).




% The following clauses serve to provide some primitive tracing facilities.
% The tracing options provided are
%  clause  - prints the current clause being considered
%  goal    - prints the current goal being considered
%  interp  - extra information about the interpreter
%  unifier - shows the unification process.

% These predicates are used to implement the special predicates trace
% and untrace.
   hp_trace(Option) :-
          (Option = allopts, !, hp_trace_all ;
           retract(hp_trace_options(L)), join([Option],L,K), 
                                      assert(hp_trace_options(K))).

   hp_untrace(Option) :-
          (Option = allopts, !, hp_untrace_all ;
 	   retract(hp_trace_options(L)), lp_remove_first(Option,L,K), 
                                              assert(hp_trace_options(K))).

   hp_untrace_all :- 
             !, retract(hp_trace_options(_)), assert(hp_trace_options([])).

   hp_trace_all :- 
         !, retract(hp_trace_options(_)),
            assert(hp_trace_options([clause,goal,interp,unifier])).

   hp_trace_options([]).

   hptrace(Opt,Kind,Comment,Thing) :- 
          hp_trace_options(L), lp_member(Opt,L), nl, write(Comment), 
          (Kind=misc, write(Thing),!;
           Kind=term, nl, write_term_lp(Thing,main),!;
           Kind=goal, nl, write_goal(Thing,main),!;
           Kind=termlist, write_term_lplist(Thing,main),!;
           Kind=subs, write_subs(Thing,main),!;
           Kind=node, write_node(Thing,main),! ;
	   Kind=frpair, nl, write_pair(Thing,main), !),
           nl,!.
   hptrace(_,_,_,_) :- !.




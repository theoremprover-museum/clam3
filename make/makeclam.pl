/*
 * @(#)$Id: makeclam.pl,v 1.2 2008/05/23 18:49:57 smaill Exp $
 *
 * $Log: makeclam.pl,v $
 * Revision 1.2  2008/05/23 18:49:57  smaill
 * port to sicstus v4
 *
 * Revision 1.1.1.1  2008/05/21 16:53:25  smaill
 * put clam3 under cvs
 *
/* This file is a script for creating an executable image of CLaM.  */
 
:- dynamic compile_and_save_clam/1.

compile_and_save_clam(Type) :-
    dialect(sic),!,
    prolog_flag(redefine_warnings,_,on),
    prolog_flag(single_var_warnings,_,off),
%   there are a lot of singelton vars here ...
    (Type = clamlib -> ['../dialect-support/sic/libs.pl']; true),
    consult('.sourcelist'),
    files_to_load(Files),
    loadc(Files),
    %% Construct banner, construct file name to save in, and save: 
    (Type = clamlib -> 
     (write('Saving core Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clamlib', "CLaM proof planner (core only)", clamlib),
	    halt)));
     (write('Saving Clam'),nl,
      call((retractall(compile_and_save_clam(_)),
	    abolish(files_to_load/1,[force(true)]),
	    save_clam('clam', "Clam proof planner", clam))) )).



/*
 *  Default method sets
 */

:- delete_methods, delete_submethods.
:- uniq_recorda(lemma_cnt,1,_).
:- uniq_recorda(hov_cnt,1,_).

load_ind_plan(1):-
	delete_methods,delete_submethods,
	lib_load(mthd(elementary/1)),
        lib_load(mthd(normal/1)),
        lib_load(mthd(equal/2)),
	lib_load(mthd(eval_def/2)),
	lib_load(mthd(fertilize/1)),
	lib_load(mthd(wave/2)),
        lib_load(mthd(generalise/2)),
	lib_load(mthd(induction/2)),
	list_methods.

:- load_ind_plan(1).



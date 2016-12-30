startup:-
    consult('~/TheoremProvers/clam/object-level/sicstus.pl'),
    consult('~/TheoremProvers/clam/object-level/oyster.pl'),
    consult('~/TheoremProvers/clam/low-level/lowlev.pl'),
    consult('~/TheoremProvers/clam/low-level/noise.pl'),
    consult('~/TheoremProvers/clam/low-level/nested_ops.pl'),
    consult('~/TheoremProvers/clam/dialect-support/sic/boot.pl'),
    consult('~/TheoremProvers/clam/dialect-support/sic/libs.pl'),
    consult('~/TheoremProvers/clam/dialect-support/sic/sysdep.pl'),
    consult('~/TheoremProvers/clam/low-level/free_vars.pl'),
    consult('~/TheoremProvers/clam/low-level/nuprlterm.pl'),
    consult('~/TheoremProvers/clam/low-level/guess_type.pl'),
    consult('~/TheoremProvers/clam/low-level/instan.pl'),
    consult('~/TheoremProvers/clam/low-level/sub_term.pl'),
    consult('~/TheoremProvers/clam/low-level/one_way.pl'),
    consult('~/TheoremProvers/clam/planner/util.pl'),
    consult('~/TheoremProvers/clam/planner/library.pl'),
    consult('~/TheoremProvers/clam/planner/method_db.pl'),
    consult('~/TheoremProvers/clam/planner/critic_db.pl'),
    consult('~/TheoremProvers/clam/planner/planner.pl'),
    consult('~/TheoremProvers/clam/planner/writef.pl'),
    consult('~/TheoremProvers/clam/meta-level/elementary.pl'),
    consult('~/TheoremProvers/clam/meta-level/reduction.pl'),
    consult('~/TheoremProvers/clam/meta-level/cancellation.pl'),
    consult('~/TheoremProvers/clam/meta-level/schemes.pl'),
    consult('~/TheoremProvers/clam/meta-level/recursive.pl'),
    consult('~/TheoremProvers/clam/coclam/meta-level/wave_fronts.pl'),
    consult('~/TheoremProvers/clam/coclam/meta-level/wave_rule_parser_new.pl'),
    consult('~/TheoremProvers/clam/coclam/meta-level/method_pre.pl'),
    consult('~/TheoremProvers/clam/meta-level/method_con.pl'),
    consult('~/TheoremProvers/clam/meta-level/methodical.pl'),
    consult('~/TheoremProvers/clam/coclam/meta-level/critics_pre.pl'),
    consult('~/TheoremProvers/clam/meta-level/disprover.pl'),
    consult('~/TheoremProvers/clam/meta-level/wave_rule_match.pl'),
    consult('~/TheoremProvers/clam/meta-level/hou.pl'),
    consult('~/TheoremProvers/clam/meta-level/convert.pl'),
    consult('~/TheoremProvers/clam/lprolog/parameters.pl'),
    lib_set(dir('~/TheoremProvers/clam/coclam/lib')),
    consult('~/TheoremProvers/clam/coclam/lib/needs.pl'),
	consult('~/TheoremProvers/clam/coclam/coinduction_lts.pl'),
	consult('~/TheoremProvers/clam/coclam/gfp_lts.pl'),
	consult('~/TheoremProvers/clam/coclam/utilities.pl'),
	consult('~/TheoremProvers/clam/coclam/lib/needs.pl'),
	consult('~/TheoremProvers/clam/coclam/gen_critic.pl'),
	consult('~/TheoremProvers/clam/coclam/meta-level/wave_rule_parser.pl'),
	consult('~/TheoremProvers/clam/coclam/meta-level/wave_rules_me.pl'),
	consult('~/TheoremProvers/clam/coclam/wave_terms_at.pl'),
	consult('~/TheoremProvers/clam/coclam/lang_lnt.pl'),
	consult('~/TheoremProvers/clam/coclam/data_lnt.pl'),
	consult('~/TheoremProvers/clam/coclam/meta-level/cases.pl'),
	consult('~/TheoremProvers/clam/coclam/intro_lts.pl'),
	consult('~/TheoremProvers/clam/coclam/transition.pl'),
	consult('~/TheoremProvers/clam/coclam/tidy_lam.pl'),
	consult('~/TheoremProvers/clam/coclam/meta-level/fert.pl'),
%	lib_delete(mthd(induction/2)),
%	lib_delete(mthd(wave/2)),
%	lib_delete(mthd(generalise/2)),
%	lib_delete(mthd(eval_def/2)),
	lib_load(mthd(elementary/1)),
        lib_load(mthd(normal/1)),
        lib_load(mthd(equal/2)),
	lib_load(mthd(fertilize/1)),
	lib_load(mthd(strong/1)),
	lib_load(mthd(gfp_membership/1)),
	lib_load(mthd(eval_def/2)),
	lib_load(mthd(transition/1)),
	lib_load(mthd(apply_lemma/1)),
	lib_load(mthd(intro1/2)),
	lib_load(mthd(wave/2)),
	lib_load(mthd(coinduction_lts/1)),
	lib_load(critic(wave/1)).

cases:- consult('~/TheoremProvers/clam/coclam/meta-level/cases.pl').
inc:- consult('~/TheoremProvers/clam/coclam/intro_lts.pl').
gfp:- consult('~/TheoremProvers/clam/coclam/gfp_lts.pl').
co:- consult('~/TheoremProvers/clam/coclam/coinduction_lts.pl').
util:- consult('~/TheoremProvers/clam/coclam/utilities.pl').
lang:- consult('~/TheoremProvers/clam/coclam/lang_lnt.pl').
tran:- consult('~/TheoremProvers/clam/coclam/transition.pl').
genc :- consult('~/TheoremProvers/clam/coclam/gen_critic.pl').

%% translate:-consult('~/Isabelle/translate.pl').
%% pp:-consult('~/Isabelle/parse_plan.pl').
%% object:-consult('~/Isabelle/object_tran.pl').
%% method:-consult('~/Isabelle/methodtotactic.pl').
%% transtuff:-translate, pp, object, method.



appn_stuff:- lib_load(wave(sapn2thm)),
	     lib_load(def(sapn)),
	     lib_load(wave(hitlem1)),
	     lib_load(def(mapapn)),
	     lib_load(def(apn)),
	     lib_load(wave(conslem1)),
	     lib_load(def(conapn)),
	     lib_load(wave(ssapn2thm)),
	     lib_load(def(ssapn)),
	     lib_load(wave(plusapn2thm)),
	     lib_load(def(plusapn)),
	     lib_load(wave(timesapn2thm)),
	     lib_load(def(timesapn)),
	     lib_load(def(idnatapn)).

stat_plan(Thm, CPU) :- statistics(runtime, _), plan(Thm), statistics(runtime, [_, CPU]).

startup:-
	lib_set(dir('~/xclam/lib')),
	consult('~/xclam/coinduction.pl'),
	consult('~/xclam/gfp_lts.pl'),
	consult('~/xclam/utilities.pl'),
	consult('~/xclam/lib/needs.pl'),
	consult('~/xclam/gen_critic.pl'),
	consult('~/xclam/wave_rule_parser.pl'),
	consult('~/xclam/wave_rules_me.pl'),
	consult('~/xclam/wave_terms_at.pl'),
%%	consult('~/xclam/in_tail_lts.pl'),
	consult('~/xclam/lang_lnt.pl'),
	consult('~/xclam/data_ind.pl'),
	consult('~/xclam/cases.pl'),
	consult('~/xclam/intro_lts.pl'),
	consult('~/xclam/transition.pl'),
	consult('~/xclam/tidy_lam.pl'),
	consult('~/xclam/fert.pl'),
	lib_delete(mthd(induction/2)),
	lib_delete(mthd(wave/2)),
	lib_delete(mthd(generalise/2)),
	lib_delete(mthd(eval_def/2)),
	lib_load(mthd(fertilize/1)),
	lib_load(mthd(strong/1)),
	lib_load(mthd(eval_def/2)),
	lib_load(mthd(transition/1)),
	lib_load(mthd(apply_lemma/1)),
	lib_load(mthd(intro1/2)),
	lib_load(mthd(wave/2)),
	lib_load(mthd(coinduction_lts/2)),
	lib_load(mthd(gfp_membership/1)),
	lib_load(mthd(induction/2)),
	lib_load(critic(wave/1)).

cases:- consult('~/xclam/cases.pl').
inc:- consult('~/xclam/intro_lts.pl').
gfp:- consult('~/xclam/gfp_lts.pl').
co:- consult('~/xclam/coinduction.pl').
util:- consult('~/xclam/utilities.pl').
deb:- consult('~/xclam/wibble.pl').
lang:- consult('~/xclam/lang_lnt.pl').
tran:- consult('~/xclam/transition.pl').

translate:-consult('~/translate/translate.pl').
pp:-consult('~/translate/parse_plan.pl').
object:-consult('~/translate/object_tran.pl').
method:-consult('~/translate/methodtotactic.pl').
transtuff:-translate, pp, object, method.



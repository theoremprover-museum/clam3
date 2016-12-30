
create_wave_rule:-
        lib_load(def(app)),
	add_def(map(a,b) <==> void),
	add_def(take(a,b) <==> void),
        add_def(drop(a,b) <==> void),
        add_def('MVar'(a,b,c) <==> void),
        add_thm(gregs, []==> f : (pnat list => pnat list) => l : pnat list => n:pnat => map(f, l)),
        add_thm(spec_rule, []==> x:pnat => y:pnat list => y = 'MVar'(drop(x,y),x,y) in pnat list),
        add_thm(mapapp, []==> f : (pnat list => pnat list) => a:pnat list => b:pnat list => map(f,app(a,b)) = app(map(f,a), map(f,b)) in pnat list),
        record_thm(gregs, thm),
        record_thm(spec_rule, thm),
        record_thm(mapapp, thm),
        add_wave_rules(mapapp, _),
        theorem(spec_rule, Lemma, thm),
        matrix(Vars, LHS = RHS in Typ, Lemma),
        wave_fronts(RHS, [[]-[[1]]/[_,out]], AnnRHS),
	replace_universal_vars([(pnat list=>pnat list),l:pnat list], [] => LHS :=> AnnRHS in Typ, WaveRule),
        writef(' enforcing creational wave-record for spec_rule.\n'),
        uniq_recorda(wave,wave(spec_rule, WaveRule, long(eqn(left))), _),
        writef('done\n').




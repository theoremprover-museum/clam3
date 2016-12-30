
gen_false([], []).
gen_false([_|T], [false|TT]):-
	gen_false(T, TT).

subpre(Pre, SubPre):-
	subpre([], Pre, SubPre).

subpre(PreSoFar, [Pre|Rest], SubPre-RestFalse):-
	append(PreSoFar, [Pre], SubPre),
        gen_false(Rest, RestFalse).
subpre(PreSoFar, [Pre|Rest], SubPre):-
	append(PreSoFar, [Pre], NewPreSoFar),
	subpre(NewPreSoFar, Rest, SubPre).

evalpre(Pre, EPreL):-
	findall(SPre, subpre(Pre, SPre), SPreL),
	evalprelist(SPreL, EPreL).

evalprelist([], []).
evalprelist([PL-FL|Rest], AnsL):-
	findall(EPLFL, (copy(PL, CPL),
                        call_conjunction(CPL),
	                append(CPL, FL, EPLFL)),
		AllEPLFL),
        evalprelist(Rest, ERest),
	append(AllEPLFL, ERest, AnsL).
	

	
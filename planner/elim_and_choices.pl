
elim_and_choices(PreListAll, NewPreList):-
        member([wave_occ_at(_, _, _),wave_rule_match(_, _, _, _),_|_], PreListAll),!,
	elim_and_choices_(PreListAll, NewPreList).
elim_and_choices(PreListAll, PreListAll).

elim_and_choices_([], []).
elim_and_choices_([H|T], NewT):-
	member(false, H),!,
        elim_and_choices_(T, NewT).
elim_and_choices_([H|T], [H|NewT]):-
	H = [wave_occ_at(_, Pos, _),
             wave_rule_match(_, _, _, _),
             _|_],!,
        elim_occs(Pos, T, NewT1),
        elim_and_choices_(NewT1, NewT).
elim_and_choices_([H|T], [H|NewT]):-
        elim_and_choices_(T, NewT).

elim_occs(Pos, [], []).
elim_occs(Pos, [H|T], NewT):-
        \+ member(false, H),
	H = [wave_occ_at(_, NPos, _),
             wave_rule_match(_, _, _, _),
             _|_],!,
        \+ Pos = NPos,
        elim_occs(Pos, T, NewT).
elim_occs(Pos, [H|T], [H|NenwT]):-
        elim_occs(Pos, T, NewT).
	
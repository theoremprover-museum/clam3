

evalpre(Pre, EPreL):-
	findall(EPre, partial_eval(Pre, EPre), EPreL).

partial_eval([Pre|RestPre], [Pre|ERestPre]):-
	call(Pre),
        partial_eval_list(RestPre, ERestPre).

partial_eval_list([], []).
partial_eval_list([Pre|Rest], [Pre|ERest]):-
        call(Pre),!,
        partial_eval_list(Rest, ERest),!.
partial_eval_list([Pre|Rest], [false|ERest]):-
        \+ call(Pre),!,
	partial_eval_list(Rest, ERest).


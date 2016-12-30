% meta_ripple_dir/2
%
%
meta_ripple_dir(Goal, Pos, NewWave):-
    matrix(_, Mat, Goal),
    exp_at(Mat, Pos, Wave),
    wave_fronts(Term, WSpec, Wave),
    select(WF-[WH]/[hard,out], WSpec, NWSpec),
    append(NWSpec, [WF-[WH]/[hard,in]], NewWSpec), 
    wave_fronts(Term, NewWSpec, NewWave),
    sinkable(NewWave),
    wave_rule(Rn, _, _ => NewWave :=> _),
    current_goaltree(Plan),
    current_node(Plan, Addr),
    \+ ancestor_method(Plan, Addr, wave(_, [Rn, _])).

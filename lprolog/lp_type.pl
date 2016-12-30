    % lp_type/3 calculates the type (lp) associated with 
    % the argument at position [ArgPos|TermPos] within the
    % formula Form.
lp_type(Form, [ArgPos|TermPos], Type):-
    exp_at(Form, TermPos, Term),
    functor(Term, F, N),
    ArgPos =< N,
    type(clam, F, Arity),
    arity2list(Arity, TypeL),
    nth1(ArgPos, TypeL, Type).

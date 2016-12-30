/*
 * This file contains all the code needed to deal with reduction rules.
 * Reduction rules are rewrite rules which are particularly well
 * behaved, and which are used in the symbolic evaluation method for
 * doing simple rewrites on expressions.
 *
 * A reduction rule is a rule which either removes a constant
 * expression, or which is a wave rule where the wave front is a type
 * constructor.
 * 
 * Just as wave-rules, reduction rules are stored at load time.
 * This is done by the predicate add_reduction_rule/1, called from the
 * library mechanism in library.pl
 */

add_reduction_rule(RuleName) :-
    is_a_reduction_rule(RuleName,Exp,Rule,Pos),
    writef(' adding reduction-record for %t...%f',[RuleName]),
    uniq_recorda(reduction,reduction(Exp,RuleName:Rule,Pos),_),
    writef('done\n').

        % is_a_reduction_rule(+RuleName,?Exp,?Rule,?Pos) RuleName is the
        % name of an equation which is a reduction rule. Rule is the equation,
        % with all universally quantified variables replaced by
        % meta-(Prolog) variables, Exp is the lhs of the equation, with
        % ditto replacement, and Pos is the position affected by the
        % rewrite (ie. the constant or constructor). 
        %
        % A reduction rule is a rule which either removes a constant
        % expression, or which is a wave rule where the wave front is a type
        % constructor.
        %
        % First clause tests for wave rules with constructor wave fronts.
/*
is_a_reduction_rule(RuleName,L,C=>L:=>R,Pos) :-
    is_a_wave_rule(RuleName,WC=>WL:=>WR,left,NList,BiList,XW,_),
    \+ member( _-[_|_]-_-_, XW ),
    nth1(N,BiList,Bi), oyster_type(_,Constructors,_), member(Bi,Constructors),
    nth1(N,NList,Pos),
    wave_fronts(C=>L:=>R,_,WC=>WL:=>WR).
*/
        % Second clause tests for rules removing constants.
        % Notice that we also require that all function symbols in the
        % rhs are lower in the gaze-graph than the function symbol of
        % the lhs. 
is_a_reduction_rule(RuleName,L1,MC=>L1:=>R1,CPos) :-
    recorded(theorem,theorem(_,_,Eq,RuleName),_),
    precon_matrix(Vars,C=>L=R in _,Eq),
    exp_at(L,CPos,Con),                                    % canonical(Con), WARNING
    findall(RFunctor,exp_at(R,[0|_],RFunctor),RFunctors),
    functor(L,LFunctor,_),
    % WARNING
    % \+ member(LFunctor,RFunctors),
    % \+ (member(RFunctor,RFunctors), needed(def(RFunctor),def(LFunctor))),
    decolon_preconds( C, DC ),
    replace_universal_vars(Vars,[DC,L:=>R],[MDC,L1:=>R1]),
    decolon_preconds( MC, MDC ).

add_equal_rule(RuleName) :-
    is_a_equal_rule(RuleName,Exp,Rule),
    writef(' adding equal-record for %t...%f',[RuleName]),
    uniq_recorda(equal,equal(Exp,RuleName:Rule),_),
    writef('done\n').

        % is_a_equal_rule(+RuleName,?Exp,?Rule) RuleName is the
        % name of a lemma which is an equal rule. Rule is the 
        % rule expressed as a directional rewrite 
        % with all universally quantified variables replaced by
        % meta-(Prolog) variables, Exp is user-defined
        %
        % An equal rule is a lemma which expresses the equivalence
        % between some sentence and an equality.
        % The idea is that we always want to know about the
        % equality because that can be applied by a variety of
        % rewriting strategies.
        % 
is_a_equal_rule( RuleName, Exp, Exp :=> Rhs ) :-
    recorded(theorem,theorem(_,_,Eq,RuleName),_),
    matrix(Vars,(T1=>T2)#(T2=>T1),Eq),
    ( ( T2 = ( _ = _ in _), T1 \= ( _ = _ in _),
        L = T1, R =T2 );
      ( T1 = ( _ = _ in _), T2 \= ( _ = _ in _),
        L = T2, R =T1 )
    ),
    replace_universal_vars( Vars, L:=>R, Exp:=>Rhs ).




/*
 * This file contains all the code needed to deal with cancellation rules.
 * Cancellation rules are rewrite rules which are particularly useful for
 * post-fertilization rippling.
 *
 * A cancellation rule corresponds to an instance of a substitution rule.
 *
 * Just as wave-rules, cancellation rules are stored at load time.
 * This is done by the predicate add_cancellation_rule/1, called from the
 * library mechanism in library.pl
 */

add_cancel_rule(RuleName) :-
    is_a_cancel_rule(RuleName,Exp,Rule),
    writef(' adding cancel-record for %t...%f',[RuleName]),
    uniq_recorda(cancel,cancel(Exp,RuleName:Rule),_),
    writef('done\n').
add_cancel_rule(_).

        % An cancellation rule is a lemma which expresses how
        % a term may be whole or partly cancelled - replace by
        % an instance of a subterm non-trivially nested within it.
        % 
/*
%%% Note: Removed because introduced unsound cancellation
%%%       rules (cf pwave). A. Ireland 3/4/92
is_a_cancel_rule( RuleName, Lhs, MC=>Lhs :=> Rhs ) :-
    recorded(theorem,theorem(_,_,Eq,RuleName),_),
    precon_matrix( Vars, C=>L=R in _, Eq ),
    decolon_preconds( C, DC ),
    replace_universal_vars( Vars, [DC,L,R],[MDC,ML,MR] ),
    ( \+ \+ exp_at( L, [_|_], MR ), Lhs = ML, Rhs = MR ;
      \+ \+ exp_at( R, [_|_], ML ), Lhs = MR, Rhs = ML 
    ),
    decolon_preconds( MC, MDC ).
*/

is_a_cancel_rule( RuleName, Lhs, MC => Lhs :=> Rhs ) :-
    recorded(theorem,theorem(_,_,Eq,RuleName),_),
    precon_matrix( Vars, C=> (LL = LR in LT)  => (RL = RR in RT), Eq ),
    decolon_preconds( C, DC ),
    replace_universal_vars( Vars, [DC,LL,LR,RL,RR],[MDC,MLL,MLR,MRL,MRR] ),
    exp_at(RL,[_|_],LL), 
    exp_at(RR,[_|_],LR), Lhs = (MRL = MRR in RT), Rhs = (MLL = MLR in LT),
    decolon_preconds( MC, MDC ).


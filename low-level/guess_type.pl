/*****************************************
 *					 *
 *  CLAM version 3.2			 *
 *					 *
 *****************************************/

%=====================================================================
% Everything to do with guessing types. Code originally from Jane.
% Lots of changes by Frank. It's a mess.

%  what will this do with nested lists?

% Frankh: Sigh... list_type/1 is used all over the place and is far too
% naive. Added kludge to make primefac work: if Type turns out to be a
% subset type, then use the type over which the subset is defined
% instead. 
list_type(Type list) :-
    do_list_type(Type1),
    ((Type1 = {_:Type\_},!)
     ;
     Type1 = Type
    ).
do_list_type(Type) :- goal(G),
                        hyp_list(H),
                        ((appears(Type list,allof(G,H)),!) ;
                         (appears(list_ind,allof(G,H)),
			  sub_term(_:R,G),
			  R =.. [=>,Type,_],
			  !)).
int_or_pnat(NumType) :-
             goal(G),
             hyp_list(H),
	     ((appears(pnat,allof(G,H)), NumType = pnat, !)
	       ; (appears(int,allof(G,H)), NumType = int, !)).

get_base_value(p_ind,0).
get_base_value(ind,0).
get_base_value(list_ind,nil).

guess_type(X,XType) :- guess_immediate_type(X,XType),!.
% next by trying obvious values (only for monadic functors)
guess_type(X,XType):- X=..[F,A],guess_type(A,AT),guess_immediate_type(I,AT),
                      ground(I),
                      Y=..[F,I],eval(Y,YY), \+ (YY=X), guess_type(YY,XType),!.
guess_type(X,XType) :-
    functor(X,F,N),
    definition(F/N <==> R),
    guess_type(R,XType).
guess_type(lambda(_,Term),TermType) :-
    guess_type(Term,TermType).
guess_type((L\R),XType) :-
    (guess_type(L,XType)
    ;guess_type(R,XType)
    ).
guess_type(term_of(Thm),Type) :- 
	ctheorem(Thm) =: problem(_==>Type,_,_,_),!.
guess_type(term_of(Thm) of _,Type) :- 
	ctheorem(Thm) =: problem(_==>_:_ => Type,_,_,_),!.
guess_type(term_of(Thm) of _ of _,Type) :- 
	ctheorem(Thm) =: problem(_==>_:_ => _:_ => Type,_,_,_),!.
guess_type(_ in Type,XType) :- super_type(Type,XType).   
guess_type(F of _,CoDomain) :- guess_type(F,_=>CoDomain).
guess_type(F of Arg,XType) :-
    \+ noprove =: _,
    eval(F of Arg,Y), \+ ((F of Arg) = Y), guess_type(Y,XType).
guess_type(Term,Type) :-
    \+ noprove =: _,
    guess_type_from_context(Term,Type).




guess_immediate_type(0,Type) :- int_or_pnat(Type).              % 0
guess_immediate_type(nil, Type) :- list_type(Type).             % nil
guess_immediate_type(s(_),pnat) :- !.
guess_immediate_type(void,u(1)).
guess_immediate_type(true,u(1)).
guess_immediate_type((_::_),Type) :- list_type(Type).
guess_immediate_type(ind(R,D,B,U),_) :-
    writef('\n** failed to guess type of %t **\n',[ind(R,D,B,U)]).
guess_immediate_type(p_ind(_,B,[_,_,S]),Type) :-
    (guess_type(B,Type)
    ;guess_type(S,Type)
    ).
guess_immediate_type(list_ind(_,B,[_,_,_,S]),Type) :-
    (guess_type(B,Type)
    ;guess_type(S,Type)
    ).

guess_type_from_context(Term,Type) :- % from hypothesis
    hypothesis(Term:Type).   
guess_type_from_context(Term,Type) :- % from goal
    goal(Goal),matrix(Vars,_,Goal),member(Term:Type,Vars).

super_type(pnat,u(1)).
super_type(_ list,u(1)).
super_type(int,u(1)).
super_type(u(I),u(J)) :- J is I + 1.
super_type(_,u(1)).                           % yuk

guess_def_types(LHS,VarTypes):-
    LHS =.. [F|Vs],
    definition(LHS <==> RHS),
    guess_def_types(Vs,F,RHS,VarTypes).

guess_def_types([],_,_,[]).
guess_def_types([V|Vs],F,RHS,[type(V,Type)|Types]):-
    guess_def_type(V,F,RHS,Type),
    guess_def_types(Vs,F,RHS,Types).

% New clause added by frankh: if RHS is a list_ind term and we are
% guessing the type of the inductive variable, then try to guess the
% type of the head-variable in the inductive term and stick 'list' at
% the end of it.
guess_def_type(V,_,list_ind(V,_,[H,_,_,Step]),Type list) :-
    		    guess_def_type(H,_,Step,Type).
/*
% New clause added by frankh: temporarily removed since not needed (yet)
% Try to guess type of inductive variable by guessing the type of the
% predecessor in the recursive term. First two conjuncts check if RHS is
% an induction functional with V as the inductive variable. Then find
% the predecessor variable using recursive_arg_with_same_type_as_ind_var/2,
% and guess its type.
guess_def_type(V,_,RHS,Type) :-
    		    analyse_induction_functional(RHS,[_|Steps]),
                    RHS =.. [_,V|_],
		    member(Step,Steps),
		    recursive_arg_with_same_type_as_ind_var(RHS,Arg),
		    guess_def_type(Arg,_,Step,Type).
*/
% rest of clauses from Jane.
guess_def_type(V,_,RHS,Type) :-
                    RHS =.. [IndType,V|_],             % induction variable
                    induction_type_over(IndType,Type), !.
guess_def_type(V,_,RHS,Type) :-                        % explicit value of fn
                    analyse_induction_functional(RHS,Outputs),
		    member(V,Outputs),
		    guess_immediate_type(RHS,Type)/*, !*/.
guess_def_type(V,_,RHS,Type) :-                        % other variables
                    sub_term(RHS,X),
		    (X = ( V = _ in Type)
		    ;X = ( _ = V in Type)
                    ;(X =.. [Functor|Args],
                      nth1(N,Args,V),
		      def_arg_type(Functor,N,Type))).

induction_type_over(p_ind,pnat).
induction_type_over(ind,int).
induction_type_over(list_ind,Type) :- list_type(Type).

analyse_induction_functional(p_ind(_,B,[_,_,S]),[B,S]).
analyse_induction_functional(list_ind(_,B,[_,_,_,S]),[B,S]).
analyse_induction_functional(ind(_,[_,_,S1],B,[_,_,S2]),[B,S1,S2]).

% Added by frankh to support extra clause for guess_def_type.
recursive_arg_with_same_type_as_ind_var(p_ind(_,_,[V,_,_]),V).
recursive_arg_with_same_type_as_ind_var(list_ind(_,_,[_,V,_,_]),V).
recursive_arg_with_same_type_as_ind_var(ind(_,[V,_,_],_,_),V).
recursive_arg_with_same_type_as_ind_var(ind(_,_,_,[V,_,_]),V).

def_arg_type(s,_,pnat):- !.
def_arg_type('::',1,Type):- !, list_type(Type list).
def_arg_type('::',2,Type):- !, list_type(Type).
def_arg_type(F,N,Type):-
    definition(F/A <==> _), functor(X,F,A),
    definition(X <==> Y),
    type_of_nth_arg_of_term(N,X,Y,Type).

type_of_nth_arg_of_term(N,Left,Right,Type):-
    Left =.. [F|Args],
    nth1(N,Args,V),
    guess_def_type(V,F,Right,Type).

% find highest mentioned universe 

top_univ_level(Term,I) :- top_u_level([Term],1,I).
top_u_level([],I,I).
top_u_level([u(J)|R],I,K) :- !, II is max(I,J),
                             top_u_level(R,II,K).
top_u_level([H|T],I,K) :- atom(H), !,top_u_level(T,I,K).
top_u_level([H|T],I,K) :- H=..[_|Args], append(Args,T,TL),
                          top_u_level(TL,I,K).




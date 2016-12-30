  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%  				FILE TERMS.PL                                 %
%                             -----------------                               %
%                                                                             %
%  Various logically meaningful operations in types and lambda terms as       %
%  represented internally by lambda Prolog are contained in this file. The    %
%  main categories of operations are the following:                           %
%                                                                             %
%       (1) Operations pertaining to types				      %
%       (2) Operations that determine free variables, and such like, in terms %
%       (3) Generating new variables needed at various stages		      %
%       (4) Substitutions and beta-normalisations       		      %
%       (5) Eta-normalisation						      %
%       (6) Converting to Huet's representation (i.e. unification-normal form)%
%	(7) Operations on substitutions					      %
%	(8) Miscellaneous operations on terms				      %
%	(9) Clause related predicates					      %
%                                                                             %
%  Operations defined here are used in UNIFY.PRO, INT.PRO, and PARSER.PRO.    %
%  The only file necessary for this file is cprolog.ini. The predicates       %
%  defined there and needed here are lp_remove_first, join, and remainder.       %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%                 OPERATIONS PERTAINING TO TYPES


% Finding the target and arguments types of a type. The target type of
% t1 --->...---> tn ---> t0 is t0 and the arguments types [t1,...,tn].
     target_and_args_type(T,T,[]) :- var(T),!.
     target_and_args_type(T1 ---> T2,T,[T1|L]) :- !,target_and_args_type(T2,T,L).
     target_and_args_type(T,T,[]) :- !.



% Checking if a term has a type variable. Is it necessary to check at any
% but the function level? I.e. can the last line in type_var_in_type be left
% out?
   type_var_in_term(A ^ B) :-
             (type_var_in_term(A);type_var_in_term(B)).
   type_var_in_term(A\B) :-
             (type_var_in_term(A);type_var_in_term(B)).
   type_var_in_term(cv(Tok,Type,CV)) :-
                          type_var_in_type(Type).

% Checking if a type expression contains a type variable.
   type_var_in_type(A) :- var(A), !.
   type_var_in_type(A ---> B) :- (type_var_in_type(A) ; type_var_in_type(B)), !.
   type_var_in_type(A ^ B) :-  (type_var_in_type(A) ; type_var_in_type(B)), !.


% Finding the type of a lambda term
     lp_type_of(cv(Token,Ty,Cv),Ty) :- !.
     lp_type_of(cv(Token,Ty1,v)\Term,Ty1 ---> Ty) :- lp_type_of(Term,Ty), !.
     lp_type_of(A ^ B, Ty1) :- lp_type_of(A,Ty2 ---> Ty1), lp_type_of(B,Ty2), !.




%            FINDING FREE VARIABLES AND SUCH OPERATIONS

% Checking if a given variable occurs free in a term
     free_occ(V,A ^ B) :- free_occ(V,A),!.
     free_occ(V,A ^ B) :- free_occ(V,B),!.
     free_occ(Var,Var\ A)  :- !,fail.
     free_occ(V,X\ A)  :- free_occ(V,A),!.
     free_occ(Var,Var) :-  !.

% Do a free_occ over a list.  Succeed if some lp_member of the list of
% terms contains Var free.  Do not resucceed.

     free_occ_list(Var,[Term|Terms]) :- free_occ(Var,Term), !.
     free_occ_list(Var,[_|Terms]) :- free_occ_list(Var,Terms).



     variable_names(cv(_,_,c),[]) :- !.
     variable_names(cv(Token,_,v),[Token]) :- !.
     variable_names(Var\Term,NL) :- 
        variable_names(Var,NL1), variable_names(Term,NL2), join(NL1,NL2,NL), !.
     variable_names(Term1 ^ Term2,NL) :- 
	variable_names(Term1,NL1), variable_names(Term2,NL2), 
	join(NL1,NL2,NL), !.

% Finding the free variables in a term; result is a `set', i.e. a list 
% in which there are no multiple occurrences.
     free_variables(cv(Token,Ty,c),[])  :- !.
     free_variables(cv(Token,Ty,v),[cv(Token,Ty,v)]) :- !.
     free_variables(Var\Term,L) :- 
		free_variables(Term,K), lp_remove_first(Var,K,L), !.
     free_variables(A ^ B, M) :- 
		free_variables(A,L), free_variables(B,K), join(L,K,M), !.


% Finding the set of variables free in a list of lambda terms
     free_variables_list([],[]).
     free_variables_list([Term|L],M) :- 
        free_variables(Term,Vlist),free_variables_list(L,K),join(Vlist,K,M),!.


% The following two predicates are used to determine when bound variables are 
% to be renamed so that Prolog terms representing distinct lambda Prolog 
% variables are not unifiable. 

% same_name_occurs(Var,Term) is true if a variable of (ostensibly) different
% type but bearing the same name as (the name of) Var occurs in Term. 
   same_name_occurs(cv(Name1,Type1,v), cv(Name1,Type2,v)) :-
                                             \+(Type1 == Type2), !.
   same_name_occurs(cv(Name1,Type1,CV),cv(Name2,_,_) \ Body) :-
             !, (Name1 = Name2 ; same_name_occurs(cv(Name1,Type1,CV),Body)), !.
   same_name_occurs(Var, Term1 ^ Term2) :- 
             !, (same_name_occurs(Var,Term1) ; same_name_occurs(Var,Term2)), !.

% name_occurs_in_list(Var,List) is true if List contains a variable with the 
% same name as that of Var.
   name_occurs_in_list(cv(Name,_,_),[Name|L]) :- !.
   name_occurs_in_list(Var,[_|L]) :- !, name_occurs_in_list(Var,L).


% rigid_path(Var, Term) succeeds if there is a rigid path (see Huet
%  TCS V1 paper) for Var in Term.  N.B.  This is not exactly the same
%  as Huet's definition since rigid_path(X,X), for variable X, succeeds.
 
rigid_path(Var,Term) :- rigid_path(Var,Term,[]).
rigid_path(Var,Term,Binder) :- 
  huet_normal(Term,hn(B,H,TermList)),
  (  lp_member(Var,B), !, fail;
     Var=H, !;
     append(B,Binder,NewBinder),
         (H=cv(_,_,c),!; lp_member(H,NewBinder)),
         rigid_path_list(Var,TermList,NewBinder)
  ).


rigid_path_list(Var,[Term|Terms],Binder) :-
  rigid_path(Var,Term,Binder), !.
rigid_path_list(Var,[_|Terms],Binder) :-
  rigid_path_list(Var,Terms,Binder).




%        GENERATING NEW VARIABLES NEEDED AT VARIOUS STAGES

% Generating a new variable that has the same type as a given atom.
   new_variable(cv(X,Ty,CV),cv(Y,Ty,v)) :- lp_gensym('Var',Y), !.

% Generating a new "universal"variable that has the same type as a given atom.
% Same as above, except the name is just differ.
   new_uni_variable(cv(X,Ty,CV),cv(Y,Ty,v)) :- lp_gensym('Uvar',Y), !.


% Generating a list of new variables from a list of types 
   new_vars_from_types([],[]) :- !.
   new_vars_from_types([Ty|L],[Var|K]) :-
            new_variable(cv(_,Ty,v), Var), new_vars_from_types(L,K), !.

% Same as above, except that it is known in this case that variables cannot get
% inadvertently bound. Hence lp_gensym can be reduced to some extent. (This is
% Dale's change).
   new_bvs_from_types(Tys,Vars) :- 
	!, 
        nvl0(Tys,Vars,['W1','W2','W3','W4','W5','W6','W7','W8','W9','W10']).

   nvl0([],[],_) :- !.
   nvl0([Ty|L],[cv(Var,Ty,v)|K],[Var|M]) :- !,  nvl0(L,K,M).
   nvl0([Ty|L],[Var|K],[]) :-  new_variable(cv(_,Ty,v),Var), nvl0(L,K,M).


% Generating a new `copy' of a list of variables.
   new_vars_from_vars([],[]) :- !.
   new_vars_from_vars([Var|L],[Newvar|K]) :-
                  !, new_variable(Var,Newvar), new_vars_from_vars(L,K).





%               SUBSTITUTIONS AND BETA NORMALISATIONS. 

% The basic operation is that of substituting for a variable in a term. Using
% this beta-normalisation is defined. Then the general notion of 
% substitution is defined. Some additional procedures that may speed up 
% beta-normalisation in special cases are also defined and used.

% subst(Term,Var,A,B) is true if substituting Term for all free occurrences of
% Var in A gives B. Free variables in Term should not get inadvertently bound.
    subst(Term,Var,T,S) :-
		variable_names(Term,NL), subst1(Term,Var,T,S,NL), !.


% subst1 does the substitution with necessary alpha-conversions.
   subst1(Term,Var,Var,Term,_) :- !.
   subst1(Term,Var,cv(Token,Ty,Cv),cv(Token,Ty,Cv),_) :- !.
   subst1(Term,Var,Var\T,Var\T,_) :- !.
   subst1(Term,Var,(A ^ B),(C ^ D),Fv) :- 
        subst1(Term,Var,A,C,Fv), subst1(Term,Var,B,D,Fv), !.
   subst1(Term,Var,X\T,Y\S,Fv) :- 
	name_occurs_in_list(X,Fv), !,        % alpha-conversion is necessary
	alpha_convert(X,T,Y,U),	subst1(Term,Var,U,S,Fv), !.
   subst1(Term,Var,X\T,X\S,Fv) :- !, subst1(Term,Var,T,S,Fv).


% Essentially alpha-conversion; it is assumed here that lp_gensymed variables 
% are distinct from all existing variables. Also a special substitution is 
% needed for this case because it must be assumed that Prolog terms 
% correponding to distinct lp variables may in fact unify.
   alpha_convert(Var,Exp,NVar,NExp) :-
		new_variable(Var,NVar), alpha_subst(NVar,Var,Exp,NExp), !.


   alpha_subst(Term,Var1,Var2,Term) :- Var1 == Var2, !.
   alpha_subst(Term,Var,cv(Token,Ty,Cv),cv(Token,Ty,Cv)) :- !.
   alpha_subst(Term,Var,(A ^ B),(C ^ D)) :- 
        alpha_subst(Term,Var,A,C), alpha_subst(Term,Var,B,D), !.
   alpha_subst(Term,Var,AbstVar\T,AbstVar\T) :- AbstVar == Var, !.
   alpha_subst(Term,Var,X\T,X\S) :- !, alpha_subst(Term,Var,T,S).


% Making an alphabetic variant of an implicitly universally closed term
   rename_free_variables(T,S) :- 
		free_variables(T,L),
		new_vars_from_vars(L,K),
		replace_vars_with_vars(K,L,T,S),!.


   replace_vars_with_vars([],[],T,T) :- !.
   replace_vars_with_vars([X|L],[Y|K],T,S) :- 
		!, subst1(X,Y,T,R,[]), replace_vars_with_vars(L,K,R,S).





% Beta normalising a lambda expression
   lnorm(cv(Tok,Ty,CV),cv(Tok,Ty,CV)).
   lnorm(Var \ Body, Var \ NormBody) :- lnorm(Body,NormBody), !.
   lnorm((Var \ Body) ^ Arg, NormTerm) :- 
		subst(Arg,Var,Body,RedBody), lnorm(RedBody,NormTerm), !.
   lnorm(Rator ^ Rand, NormTerm) :- 
		lnorm(Rator,RedRator), 
		( RedRator = Var \ Body, !,
			subst(Rand,Var,Body,RedBody), lnorm(RedBody,NormTerm) ;
		  lnorm(Rand,RedRand), NormTerm = RedRator ^ RedRand
                ), !.


% Beta normalising a list of lambda expressions
   lnorm_list([],[]).
   lnorm_list([T|L],[S|K]) :- lnorm(T,S), lnorm_list(L,K), !.




% Substituting and beta-normalising. It is assumed that the input terms are
% in beta-normal form. This procedure is useful only under the assumption 
% that substitutions perturb beta-normalisation only locally, and so local
% re-normalisation is less expensive than renormalisation of the entire term.
    subst_and_lnorm(SubsTerm,Var,InTerm,OutTerm) :-
		variable_names(SubsTerm,NL), 
		subst_and_lnorm1(SubsTerm,Var,InTerm,OutTerm,NL), !.


% Taking care of necessary alpha-conversions in substituting and normalising.
% Like in the case of subst1, it is assumed lp_gensymed variables are unique.
    subst_and_lnorm1(SubsTerm,Var,Var,SubsTerm,_) :- !.
    subst_and_lnorm1(SubsTerm,Var,cv(Tok,Ty,CV),cv(Tok,Ty,CV),_) :- !.
    subst_and_lnorm1(SubsTerm,Var,Var\Term,Var\Term,_) :- !.
    subst_and_lnorm1(SubsTerm,Var,X\Term,Y\OutTerm,FV) :-
	name_occurs_in_list(X,FV), !,        % alpha-conversion is necessary
	alpha_convert(X,Term,Y,TempTerm),
	subst_and_lnorm1(SubsTerm,Var,TempTerm,OutTerm,FV), !.
    subst_and_lnorm1(SubsTerm,Var,X\Term,X\OutTerm,FV) :-
		subst_and_lnorm1(SubsTerm,Var,Term,OutTerm,FV), !.
    subst_and_lnorm1(SubsTerm,Var,Rator ^ Rand,OutTerm,FV) :-
		subst_and_lnorm1(SubsTerm,Var,Rator,OutRator,FV),
		subst_and_lnorm1(SubsTerm,Var,Rand,OutRand,FV),
         	( OutRator = Bind \ Body, !,
			subst_and_lnorm(OutRand,Bind,Body,OutTerm) ;
		  OutTerm = OutRator ^ OutRand
		), !.
         




% Applying a substitution. The first argument in the procedures below is a 
% list that represents the substitution obtained by composing the substitution 
% pairs in the list in a right to left fashion. In all these cases, if the
% input and substitution terms are in beta (beta-eta) normal form, then the 
% result is also in the same form.

% Applying a substitution to a term
   apply_subs_to_term([],S,S) :- !.
   apply_subs_to_term([[V,Subs]|L],T,S) :- 
			!,
			subst_and_lnorm(Subs,V,T,U), 
			apply_subs_to_term(L,U,S).


% Applying a substitution to a list of terms
   apply_subs_to_list(Subs,[],[]) :- !.
   apply_subs_to_list(Subs,[G|L],[H|K]) :- 
			!,
			apply_subs_to_term(Subs,G,H), 
			apply_subs_to_list(Subs,L,K).

% Applying a substitution to a list of pairs of terms
   apply_subs_to_pairlist(Sub,[],[]) :- !.
   apply_subs_to_pairlist(Sub,[[E1,E2]|L],[[D1,D2]|K]) :- 
			!,
			apply_subs_to_term(Sub,E1,D1), 
			apply_subs_to_term(Sub,E2,D2),
			apply_subs_to_pairlist(Sub,L,K).

% Applying a substitution to a goal: this differs from applying to a term
% only in that some of the abstractions are in the list Uvars and not actually
% attached to the term.

   apply_subs_to_goal(Subs,Uvars,Goal,NewUvars,NewGoal) :- 
			!,
			huet_normal(Abst_Goal,hn(Uvars,Goal,[])),
			apply_subs_to_term(Subs,Abst_Goal,Abst_NewGoal),
			huet_normal(Abst_NewGoal,hn(NewUvars,NewGoal,[])).



%                   ETA-NORMALISATION OF TERMS

% In the procedures below, it is assumed that terms are input in beta-normal
% form. In some cases it is assumed that terms are in Huet's representation of
% beta-normal terms. The necessary `fluffing' up is what is done. The ONLY
% place where beta-normalisation is also done is in el_norm.


% Fluffing up a term at the top level. Input and output in `Huet' normal form.
   eta_norm_head(hn(Bnd1,Head,Args1),hn(Bnd2,Head,Args2)) :-
			Head = cv(Tok,Ty,CV), 
			target_and_args_type(Ty,TargTy,ArgsTy),
			length(Args1,N),
			( length(ArgsTy,N), !, 
				Bnd2 = Bnd1, Args2 = Args1 ;
			  remainder(ArgsTy,N,RemArgsTy), 
			  	new_vars_from_types(RemArgsTy,RemArgs),
				append(Bnd1,RemArgs,Bnd2), 
				append(Args1,RemArgs,Args2)
			).



% Fluffing up the entire term. Terms are in normal representation
   eta_norm(Term,NormTerm) :-
		huet_normal(Term,hn(Bind,Head,Args)), 
		eta_norm_list(Args,NormArgs),
		Head = cv(_,Ty,_),
		target_and_args_type(Ty,_,ArgsTy),
		length(Args,N), 
		length(ArgsTy,N1),
		( N = N1, !,
			huet_normal(NormTerm,hn(Bind,Head,NormArgs)) ;
		  remainder(ArgsTy,N,RemArgs),
			eta_normal_vars(RemArgs,RemArgVars,RemArgTerms),
			huet_normal_arg2(Term1,Head,NormArgs),
			huet_normal(Term2,hn(RemArgVars,Term1,RemArgTerms)),
			huet_normal(NormTerm,hn(Bind,Term2,[]))
		), !.


% Fluffing up a list of terms. Terms are in normal representation.
   eta_norm_list([],[]) :- !.
   eta_norm_list([Term|Terms],[NormTerm|NormTerms]) :-
			eta_norm(Term,NormTerm), 
			eta_norm_list(Terms,NormTerms), !.




% Generating a variable in eta-normal form from its type.
   eta_normal_var(Type,Var,VarTerm) :-
		new_variable(cv(_,Type,v),Var),
		target_and_args_type(Type,_,ArgTypes),
		eta_normal_vars(ArgTypes,ArgVars,ArgVarTerms),
		huet_normal(VarTerm,hn(ArgVars,Var,ArgVarTerms)), !.



% Generating a list of variables in eta-normal form from a list of types.
   eta_normal_vars([],[],[]) :- !.
   eta_normal_vars([Type|Types],[Var|Vars],[VarTerm|VarTerms]) :-
		eta_normal_var(Type,Var,VarTerm), 
		eta_normal_vars(Types,Vars,VarTerms), !.



% Converting a lambda term in normal representation into a beta-eta normal form
   el_norm(Term,NormTerm) :-
		lnorm(Term,LamNormTerm), 
		eta_norm(LamNormTerm,NormTerm), !.

% Checking if a term eta reduces to a variable or a constant and returning 
% this if it does
   eta_reduce_cv(Term, CV) :-
		huet_normal(Term,hn(B,CV,B)), (CV = cv(_,_,c) ; \+ (lp_member(CV,B))), !.






%   CONVERTING BETWEEN NORMAL TERM REPRESENTATION AND HUET'S REPRESENTATION

% huet_normal(Term,NFTerm) is true if NFTerm is of the form hn(W,H,A)
% where W is the binder, H is the head and A is the list of arguments
% in a "head normal form" representation of Term. Term is assumed to be in
% beta-normal form
   huet_normal(BV\Term, hn([BV|RBinder],Head,Args)) :- 
			huet_normal(Term,hn(RBinder,Head,Args)), !.
   huet_normal(Term, hn([],Head,Args)) :- 
			huet_normal_arg(Term,Head,Args).


% Clugy. To ensure reversibility, different procedures are used.
   huet_normal_arg(Term,Head,Args) :- 
		var(Args), !,
		huet_normal_arg1(Term,Head,Args,[]).
   huet_normal_arg(Term,Head,Args) :-
		huet_normal_arg2(Term,Head,Args).

% Finding the head and arguments of a term with no top level abstractions
   huet_normal_arg1(Term ^ Arg,Head,Args,Someargs) :-
			!, huet_normal_arg1(Term,Head,Args,[Arg|Someargs]).
   huet_normal_arg1(Head,Head,Args,Args).

% Form a term given its head and arguments. No top-level abstractions.
   huet_normal_arg2(Term,Head,[Arg|Restargs]) :-
			!, huet_normal_arg2(Term,Head ^ Arg,Restargs).
   huet_normal_arg2(Head,Head,[]).


% Convert the pairlist into a pairlist of hn forms.

hn_list([],[]).
hn_list([[F1,F2]|L],[[H1,H2]|K]) :-
	huet_normal(F1,H1), huet_normal(F2,H2), !,
	hn_list(L,K).





%		 SOME OPERATIONS ON SUBSTITUTIONS

% restrict_subs(Vars,Sub1,Sub2) is true if the compound substitution
% represented by the list Sub1 is the substitution Sub2 on the variables
% in Vars
   restrict_subs([],Sub,[]) :- !.
   restrict_subs([V|Vs],Sub,[[V,T]|K]) :- 
		apply_subs_to_term(Sub,V,T),!, restrict_subs(Vs,Sub,K).


% Composing two substitutions
   compose_subs(Sub1,Sub2,Sub3) :- append(Sub1,Sub2,Sub3),!.




%   		 MISCELLANEOUS LOGICAL OPERATIONS ON TERMS

% Forming the universal closure of a lambda term. The constant used as a 
% universal set recogniser is pi. Input term must have the right type.
   universal_closure(Term,ClosedTerm) :- 
		free_variables(Term,FV), univ_c(Term,ClosedTerm,FV),!.

   univ_c(Term,Term,[]) :- !.
   univ_c(Term,cv(pi,(Ty--->o)--->o,c)^(cv(Tok,Ty,v)\Term0),[cv(Tok,Ty,v)|L]) :-
		!, univ_c(Term,Term0,L).

% Forming the universal closure of a list of terms.
   universal_closure_list([],[]) :- !.
   universal_closure_list([Term|L],[ClosedTerm|K]) :-
		!, 
		universal_closure(Term,ClosedTerm), 
		universal_closure_list(L,K).


% Making universal quantification implicit in a term. There are two versions.
% In one case the quantifier and abstraction are dropped. In the second version
% the quantified variable is replaced by a new one. 
   univ_instan(cv(pi,Ty,c) ^ (Var \ Cl), A) :- !, univ_instan(Cl,A).
   univ_instan(A,A).

   univ_instan1(cv(pi,(Ty--->o)--->o,c) ^ (Y\B), A) :-
		!, 
                new_variable(cv(_,Ty,v),X), 
		subst(X,Y,B,C), 
		univ_instan1(C,A).
   univ_instan1(A,A).



% Making a list of the top level conjuncts in a propositional term
   conjuncts(cv(',', o ---> o ---> o,c) ^ A ^ B, M) :- 
			!, conjuncts(A,L), conjuncts(B,K), append(L,K,M).
   conjuncts(A,[A]).



% This function instantiates all the type variables which are in a goal.  
% Freezing type variables in types and terms; these are instantiated by
% new constant types labeled ty1, ty2, ...

freeze_typevar_in_term(A ^ B) :- 
         !, freeze_typevar_in_term(A), freeze_typevar_in_term(B).
freeze_typevar_in_term(A \ B) :- 
         !, freeze_typevar_in_term(A), freeze_typevar_in_term(B).
freeze_typevar_in_term(cv(Tok,Tya,CV)) :- !, freeze_typevar_in_type(Tya).

freeze_typevar_in_type(A) :- var(A),!,lp_gensym(ty,A).
freeze_typevar_in_type(A ---> B) :- 
        !, freeze_typevar_in_type(A), freeze_typevar_in_type(B).
freeze_typevar_in_type(A ^ B) :- 
        !, freeze_typevar_in_type(A), freeze_typevar_in_type(B).
freeze_typevar_in_type(_) :- !.





%  			SOME CLAUSE RELATED PREDICATES

% Is a term a lambda Prolog constant?
   is_param(cv(Tok,Type,c)) :- constant_token(Tok).

% Is a term a lambda Prolog variable?
   is_var(cv(_,_,v)).

% head_of_clause(Term,HeadPred) is true if Term is a clause that is part of the
% definition of the predicate HeadPred. This is supposed to be a syntax checker
% for the parser, and to make it complete valid_goal and valid_args have to be 
% given more teeth.
   head_of_clause(cv(Ent, o ---> o ---> o, c) ^ L ^ R, HeadPred) :-
		Ent=(':-') , !, 
			     valid_head(L,HeadPred), valid_goal(R).
   head_of_clause(Term,HeadPred) :- 
		valid_head(Term,HeadPred).


   valid_head(Term,Head) :-
		huet_normal(Term,hn(W,Head,A)), 
		is_param(Head), valid_args(A).

   valid_goal(G).

   valid_args(A).


% Finding the head and body of a clause.
   clause_head_and_body(Turnstile ^ Head ^ Body, Head,Body) :- 
						turnstile(Turnstile),!.
   clause_head_and_body(H,H,cv(true,o,c)).

% Finding the head of a term
   term_head(Term,Head) :- huet_normal(Term,hn(W,Head,A)),!.

% Dealing with "parametric variables"

   para_vars_for_free_vars(Uvars,T,S) :-
	free_variables(T,L),
	new_para_vars_from_vars(Uvars,L,K),
	replace_vars_with_para_vars(Uvars,K,L,T,S).

   new_para_vars_from_vars(Uvars,[],[]).
   new_para_vars_from_vars(Uvars,[cv(_,Ty,v)|L],[PVar|K]) :-
	new_para_var(Uvars,Ty,PVar),
	new_para_vars_from_vars(Uvars,L,K).


% new_para_var(Uvars,Type,PVar) is true if PVar is a new parametric variable
% of type Type over the parameters in Uvar.

   new_para_var([],Ty,PVar) :- new_variable(cv(_,Ty,v),PVar),!.
   new_para_var([cv(Name,Ty1,v)|L],Ty,(PVar^cv(Name,Ty1,v))) :- new_para_var(L,Ty1 ---> Ty,PVar).

% replace_vars_with_para_vars(K,L,T,S) if S is the result of replacing
% the variables in L with the corresponding one in K in the term T.

   replace_vars_with_para_vars(_,[],[],T,T).
   replace_vars_with_para_vars(Uvars,[X|L],[Y|K],T,S) :- 
	!, subst1(X,Y,T,Tmp,Uvars), replace_vars_with_para_vars(Uvars,L,K,Tmp,S).

% abst_uvars(Uvars,Term,Abst_Term) is true if Abst_Term is the result of 
% placing abstractions of the variables Uvar over Term.

abst_uvars([],T,T).
abst_uvars([X|L],T,X\S) :- abst_uvars(L,T,S).


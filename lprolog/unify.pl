  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                               FILE  UNIFY.PL                                %
%                             ------------------                             %
%                                                                             %
%  This file contains a simple implementation of higher-order unification     %
%  based on Huet's procedure as presented in the TCS article. The main        %
%  difference is that the eta rule is assumed, and a limited use of type      %
%  variables is provided. Type variable instantiations may be determined in   %
%  simpl as a consequence of matching rigid-rigid terms. Match fails in the   %
%  case that it is provided with two terms whose target types are variables.  %
%  Similarly projection fails when the target type of an argument is a        %
%  variable. 								      %
%                                                                             %
%                                                                             %
%  The provision of type variables forces us to abandon the requirement that  %
%  input terms to the unification process are in eta-normal form. What is     %
%  done instead is the following:					      %
%                                                                             %
%	(1) Binder lengths are never checked.                                 %
%	(2) Extra arguments need to be added, based on an eta 		      %
%	    normalisation at the top level, when two rigid terms are	      %
%	    are encountered in SIMPL. This is done provided the heads match.  %
%       (3) In projection and imitation the largest number of binders and     %
%           arguments are generated, based on the types of the flexible and   %
%           rigid heads.                                                      %
%                                                                             %
%  The correctness of this modified procedure seems obvious for the case when %
%   when type variables are not present, but it has to be proved rigourously. %
%                                                                             %
%                                                                             %
%  As noted above type variables cause problems in MATCH; interpreting them   %
%  as existentially quantified over all possible functional types, means that %
%  they constitute an additional source of branching. Although the points     %
%  where this branching occurs has been localised (see check_type_var_in_unif %
%  and calls to it), it is not clear how the branching should be dealt with.  %
%                                                                             %
%                                                                             %
%  The routines used in this file that have to do with types and terms and    %
%  with substitutions are to be found in TERMS.PRO.                           %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% unify(Dplist,FFlist,Subs) is true if Dplist can be reduced to the list of
% flexible-flexible disagreement pairs FFlist by virtue of the substitution 
% Subs. The terms in Dplist are assumed to be in beta-normal form. 

   unify(Dplist,FFlist,Subs) :- 
	hptrace(unifier,node,'Input disagreement set:',Dplist),
	simpl_and_triv(Dplist,Dp1,Subs1),
	hptrace(unifier,node,'Simplified and cleaned disagreement set:',Dp1),
	(Subs1 = [] ;
		hptrace(unifier,subs,'The simplifying substitution:',Subs1)),
	!,
	( fr_element(Dp1,[Flex,Rigid]), !, 
				match(Flex,Rigid,MatchSubs),
			        apply_subs_to_pairlist(MatchSubs,Dp1,Dp3), 
				unify(Dp3,FFlist,Subs2), 
			        compose_subs(MatchSubs,Subs2,Subs3), 
				compose_subs(Subs1,Subs3,Subs) ;
	  FFlist = Dp1, Subs = Subs1
	).





% simpl_and_triv attempts to simplify the input disagreement set a la Huet. It
% also looks for disagreement pairs that have a trivial MGU (explained in the 
% context of triv below). If such a pair exists, then the substitution is 
% extracted and a simplified disagreement set results, and the process is 
% repeated. Finally a simplified disagreement set and an associated 
% substitution is returned. If simplification shows that unification is 
% impossible, then simpl_and_triv fails.

simpl_and_triv(In_dplist,Out_dplist,Subs) :-
      simplify(In_dplist,Dp1), triv(Dp1,Dp2,Subs1),
      (Subs1 = [], !,
		      Subs = [], Out_dplist = Dp2 ;
       apply_subs_to_pairlist(Subs1,Dp2,Dp3),
           simpl_and_triv(Dp3,Out_dplist,Subs2),
           compose_subs(Subs1,Subs2,Subs) 
       ), !.





% Simplifying a disagreement set a la Huet

   simplify([],[]) :- !.
   simplify([[E,E]|L],K) :-
                      !, simplify(L,K).
   simplify([Pair|L],K) :-
                      lp_member(Pair,L), !, simplify(L,K).
   simplify([[T1,T2]|L],K) :-
        eta_reduce_cv(T1,V), eta_reduce_cv(T2,V), !, simplify(L,K).
   simplify([[E1,E2]|L],Simpl) :-
        huet_normal(E1,HNE1),
        (flexible(HNE1), !, 
			simplify(L,M), Simpl = [[E1,E2]|M];
	 huet_normal(E2,HNE2),
		        (flexible(HNE2), !, 
					simplify(L,M), Simpl = [[E2,E1]|M] ;
		         !, 
			 simplify_pair(HNE1,HNE2,K), append(K,L,G),
                         simplify(G,Simpl) 
 			) 
	).




%  Simplifying a RIGID-RIGID pair. In a call simplify_pair(E1,E2,L), E1 and E2
%  are expected to be in huet-normal-form (see huet_normal for the term 
%  representation), and  L is the result of a simplification on E1 and E2. 
%  Detection of non-existence of unifiers causes a failure.
%  NOTE: THIS IS THE ONLY PLACE WHERE ETA-NORMALIZATION IS REQUIRED

     simplify_pair(hn(W1,G1,A1),hn(W2,G2,A2),L) :-
            heads_equal(G1,W1,G2,W2), !,
            eta_norm_head(hn(W1,G1,A1),hn(Wp1,G1,Ap1)),
            eta_norm_head(hn(W2,G2,A2),hn(Wp2,G2,Ap2)),
            binder_over_terms(Wp1,Ap1,Wp2,Ap2,L).
              

% Checking whether the heads of two terms match; see Huet.
     heads_equal(A,L1,A,L2) :- A = cv(_,_,c), !.
     heads_equal(A,L,X,K) :-  same_binder_var(A,L,X,K).

     same_binder_var(A,[A|L],X,[X|K]) :- !.
     same_binder_var(A,[A|L],Y,[X|K]) :- !, fail.
     same_binder_var(A,[B|L],X,[X|K]) :- !, fail.
     same_binder_var(A,[X|L],B,[Z|K]) :- !, same_binder_var(A,L,B,K).


% Forming the residual terms for SIMPL when heads match. 
     binder_over_terms(_,[],_,[],[]).
     binder_over_terms(W1,[A1|K1],W2,[A2|K2],[[E1,E2]|L]) :-
		huet_normal(E1,hn(W1,A1,[])), 
		huet_normal(E2,hn(W2,A2,[])),
		binder_over_terms(W1,K1,W2,K2,L).




% Finding pairs in a reduced disagreement set for which a MGU exists. This is 
% essentially TRIV in "Higher-Order Logic Programming", ICLP 86. There is one 
% extra feature in that eta-normalization is taken into account. Also if the  
% arguments are merely a lp_permutation of the binder, then there is a simple MGU
% that is constructed. 

% In a call triv(Dpset,Newdpset,Subs), Dpset is the input disagreement set,
% Subs is a substitution that is returned, and Newdpset is Dpset with the pair
% that is solved by Subs lp_removed. 
% NOTE: The input set is assumed to be a reduced disagreement set a la Huet.
   
    triv([],[],[]).

    triv([[T1,T2]|L],L,[[cv(Tok,Ty,v),SubsTerm]]) :-
           	huet_normal(T1,hn(Binder,cv(Tok,Ty,v),Args)),
           	\+free_occ(cv(Tok,Ty,v),T2), 
		lp_permutation(Binder,Args),
           	new_vars_from_vars(Binder,NewArgs),
           	permute_vars(Binder,Args,NewArgs,NewBinder),
           	huet_normal(Term,hn(NewBinder,T2,NewArgs)), 
		lnorm(Term,SubsTerm), !.

    triv([[T1,T2]|L],L,[[cv(Tok,Ty,v),SubsTerm]]) :-
           	huet_normal(T2,hn(Binder,cv(Tok,Ty,v),Args)),
           	\+free_occ(cv(Tok,Ty,v),T1), 
		lp_permutation(Binder,Args),
           	new_vars_from_vars(Binder,NewArgs),
           	permute_vars(Binder,Args,NewArgs,NewBinder),
           	huet_normal(Term,hn(NewBinder,T1,NewArgs)), 
		lnorm(Term,SubsTerm), !.

    triv([Pair|L],[Pair|K],Subs) :- triv(L,K,Subs).


% If the second argument is a lp_permutation of the first, then the fourth is an
% identical lp_permutation of the third
   permute_vars([W|W1],W2,[U|U1],U2) :- 
             !, change_var(W,U,W2,W3), 
		permute_vars(W1,W3,U1,U2).
   permute_vars([],U,[],U).

   change_var(X,Y,[X|L],[Y|L]) :- !.
   change_var(X,Y,[Z|L],[Z|K]) :- !, change_var(X,Y,L,K).



% Checking if a term is flexible or rigid; term input in huet-normal form
   rigid(hn(Binder,cv(F,Ty,CV),Args)) :-
           (CV=c ; lp_member(cv(F,Ty,v),Binder)).

   flexible(Term) :- \+rigid(Term).




% Picking a flexible-rigid pair from a REDUCED disagreement set. Returns the
% first such pair putting the terms in huet-normal form. Fails if there
% are no such pairs
   fr_element([[F1,F2]|L],[HNF1,HNF2]) :-
	huet_normal(F2,HNF2), rigid(HNF2), !,
			 huet_normal(F1,HNF1),
		         hptrace( unifier,
				  frpair,
				  'Picking the flexible-rigid pair: ',
				  [F1,F2] ).
   fr_element([X|L],Pair) :- fr_element(L,Pair).





% Given a flexible-rigid pair <E1,E2>, producing the many substitutions defined
% by MATCH a la Huet. In a call match(E1,E2,[[Var,Term]]) E1 and E2 must be
% in huet-normal form, and [[Var,Term]] is instantiated to a substitution.
% Substitutions are produced one at a time (depth-first with backtracking), 
% with a switch controlling whether projections are to be done first or 
% imitation. If type variables need to be instantiated to determine 
% substitutions, then the user is quizzed; this is necessary only in 
% projection.

  match(hn(_,FlexHead,_),hn(_,RigHead,_),[[FlexHead,SubsTerm]]) :-
      FlexHead = cv(F,FlexType,v),
      target_and_args_type(FlexType,TargTy,ArgTys), 
      (projfirst, !,
	  (check_type_var_in_proj(TargTy,FlexType,flex), 
			projection(ArgTys,TargTy,SubsTerm) ;
           RigHead = cv(_,_,c), imitation(TargTy,ArgTys,RigHead,SubsTerm)) ;
       RigHead = cv(_,_,c), imitation(TargTy,ArgTys,RigHead,SubsTerm) ;
       check_type_var_in_proj(TargTy,FlexType,flex), 
			projection(ArgTys,TargTy,SubsTerm)),
      hptrace(unifier,subs,'Picking the substitution: ',[[FlexHead,SubsTerm]]).




% Constructing the one imitation term. 

    imitation(FlexTargTy,FlexArgTys,cv(Head,RigType,c),Term) :-
		target_and_args_type(RigType,FlexTargTy,ArgTys),
		new_bvs_from_types(FlexArgTys,BinderVars),
		general_args(ArgTys,BinderVars,FlexArgTys,Args),
		huet_normal(Term,hn(BinderVars,cv(Head,RigType,c),Args)).



% Constructing the possibly many projection substitution terms. This may fail
% if there are type variables in the type of the flexible term, or if no 
% projection is possible on account of type constraints.
    projection(BinderTys,TargTy,Term) :- 
           new_bvs_from_types(BinderTys,BinderVars),
           !,
           memb(cv(Head,Type,v),BinderVars),
           proj_args_type(Type,TargTy,ArgTys),
           general_args(ArgTys,BinderVars,BinderTys,Args),
           huet_normal(Term,hn(BinderVars,cv(Head,Type,v),Args)).


    proj_args_type(Type,TargTy,ArgTys) :-
		target_and_args_type(Type,TTargTy,ArgTys),
		check_type_var_in_proj(TTargTy,Type,arg),
		TTargTy = TargTy, !.




   check_type_var_in_proj(TargTy,Type,What) :-
	tvw, var(TargTy), !,
		(What = flex, !,
			write('PROJ substitution to be found for variable of type'),nl;
		 What = arg,
			write('Trying to project on an argument with type'),nl
		),
		write('       '), write_type(Type), nl,
                write('Do you want to go on? (y/n)'),
                (get_response(Word), Word = 'y', !,
			write('Assuming for the moment that target '),
			write('type is primitive'), nl, nl ;
		 abort
		).

   check_type_var_in_proj(_,_,_).



% general_args(Type_list,Binder,Bindertypes,Args) generates the general 
% arguments needed in MATCH. Here Binder is the binder for the substitution
% term being generated, and Bindertypes are the types of these. Typelist is
% the types of the arguments that need to be generated. 
   general_args([],_,_,[]).

   general_args([Ty|L],W,Wtypes,[A|K]) :- 
		target_and_args_type(HeadType,Ty,Wtypes),
		new_variable(cv(_,HeadType,v),Head), 
		huet_normal(A,hn([],Head,W)),
		general_args(L,W,Wtypes,K), !.

binder_over_args(_,[],[]).
binder_over_args(W,[A|K],[E|L]) :-
  huet_normal(E,hn(W,A,[])), 
  binder_over_args(W,K,L).


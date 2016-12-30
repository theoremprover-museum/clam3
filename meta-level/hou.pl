% -*- Prolog -*-
% @(#)hou.pl	2.1	(93/06/17 10:48:35)
% @(#)Higher-order utility predicates

/* first arg is a list of object variables wish to leave as meta-level constants
 * without lifting them as bound variables.  
 * note that there is no lifting going on here: use hou_rewrite if you're into
 * lifting (or see instantiate_hou, which does some lifting)
 * all that goes on is to convert H and G in LP form, and wrap these terms
 * in a Binding consisting of the free variables in G and H.  Freezers are to
 * be taken as 
 */
hou_pterms(Freezers,Subs,H,G) :-
    \+var(Freezers),
    is_grounded(H),            % ground prolog vars to explicit meta-
    is_grounded(G),            % variables X --> 'Mi' [NB this shouldn't really
                               % be needed her

    strip_meta_annotations(dummy(H),dummy(Hstrip)),  %dummy to save prolog variables
    strip_meta_annotations(dummy(G),dummy(Gstrip)),
    freevarsinterm(Hstrip,HfvMeta),
    freevarsinterm(Gstrip,GfvMeta),
    union(HfvMeta,GfvMeta,FVallMeta),         % FVs in these terms forms a binding
    remove_meta_variables(FVallMeta,FVall),
    remove_elements(Freezers,FVall,FVs),

    convert(FVs,H,Hlp),
    convert(FVs,G,Glp),

    is_bound_term(FVs,Hlp,Hbound),             % add the binding
    is_bound_term(FVs,Glp,Gbound),
    
    unify([[Hbound,Gbound]],Residue,Subs),

    free_variables(Hbound,FV1),
    free_variables(Gbound,FV2),
    union(FV1,FV2,FV).

%   restrict_subs(FV,Sbs,Subs).


/* apply a higher-order rewrite using
 * Note that any meta-varibles in R which do not occur free in L
 * are _not_ lifted over the context defined by the free (first-order) variables (FVs)
 * of H; maybe this is wrong, but for the moment, it seems to accord with
 * what I imagine such meta-variables to be.
 */
hou_rewrite(Freezers,Subs,H,L :=> R,Hnew) :-
    \+var(Freezers),
    is_grounded(H),            % ground prolog vars to explicit meta-
    is_grounded(L),            % variables X --> 'Mi'
    is_grounded(R),            % This is needed since we do not assume that
                               % FV(R) \subseteq FV(L) [see below]

    strip_meta_annotations(dummy(H),dummy(Hstrip)),  %dummy to save prolog variables
    freevarsinterm(Hstrip,FOfree),   % free fo meta-variables
    remove_meta_variables(FOfree,FVall),
    
    remove_elements(Freezers,FVall,FVs),      % FVs is the set of free-variables
                                              % in H which we do not treat as constant
 
    /* we now lift the rule L:=R over the context FVs: 
     * for each free meta-variable in L, say U, applied to (y1,y2...ym), replace with
     * U(y1,y2...ym,x1,x2,...,xn) where {x1,...,xn} == FVs
     * NB.  As mentioned above, it is necessary to consider a free-variable
     * U in R s.t. U \not\in FV(L) as a special case. Eg. Rather than lift like
     * this:
     *
     *     R = ...U(y1,y2)...     -- lift -->   R = ... U(y1,y2,x1,x2)
     *
     * we instead lift like this:
     *
     *     R = ...U(y1,y2)...     -- lift -->   R = ... U(y1,y2)
     *
     * i.e. unchanged.
     */
    make_lifted_term(_,FVs,L,Lgnd,Lfree),        % lift all meta-variables Lfree over context
    make_lifted_term(Lfree,FVs,R,Rgnd,_),        % lift all mvs in R which are free in L
    
    convert(FVs,H,Hlp),
    convert(FVs,Lgnd,Llp),

    /* make these terms we are to unify into lambda-bound terms over
     * the context defined by FVs
     */
    is_bound_term(FVs,Hlp,Hbound),
    is_bound_term(FVs,Llp,Lbound),
    
    /* ensure all bound variables are distinct
     * this is a pain, but needed since LP falls over otherwise
     */
    unique_bound_variables([],Hbound,LPH),
    unique_bound_variables([],Lbound,LPL),
    
    unify([[LPH,LPL]],Residue,Sbs),

    free_variables(LPH,FV1),
    free_variables(LPL,FV2),
    union(FV1,FV2,FV),
    restrict_subs(FV,Sbs,Subs),
    apply_subs_to_pterm(Subs,Rgnd,Hnew).

no_free([],Subs).
no_free([V:_|R],Subs) :-
    \+var_is_free_in_dom(V,Subs),
    no_free(R,Subs).

var_is_free_in_dom(V,[[_,Dom]|Rest]) :-
    free_occ(cv(V,term,c),Dom);
    var_is_free_in_dom(V,Rest).


is_bound_term([], T, T).
is_bound_term([V], T, cv(V,term,v)\T) :- !,ground(V).
is_bound_term([V|Vs], T, cv(V,term,v)\ Rest) :-
    is_bound_term(Vs,T, Rest).

make_binding([V:T],cv(Vmod,term,v),[V],[Vmod]) :- ground(V),gensym('MV',Vmod).
make_binding([V:T|Vs],cv(Vmod,term,v)\ Rest,[V|Vlist],[Vmod|Bl]) :-
    gensym('MV',Vmod),make_binding(Vs,Rest,Vlist,Bl).

write_term_lp_list(M,[]).
write_term_lp_list(M,[Name-T|Ts]) :-
    write(Name),write(' == '),write_term_lp(T,M),nl,
    write_term_lp_list(M,Ts).
write_term_lp_list(M,_) :- thisisanerror.


write_pterm_list([]).
write_pterm_list([Name-T|Ts]) :-
    write(Name),write(' == '),write(T),nl,
    write_pterm_list(Ts).
write_pterm_list(_) :- thisisanerror.


apply_subs_to_pterm(Subs,P,Pnew) :-
    convert([],P,LP),
    apply_subs_to_term(Subs,LP,LPn),
    lnorm(LPn,LPnew),
    bvs_are_obj_vars(LPnew,LPobject),
    convert([],Pnew,LPobject).

/* is_grounded(H) instantiate all prolog variables to meta-variables of the
 * form 'Mi'
 */
is_grounded(V) :-
    gensym('M',V),!.
is_grounded(T) :-
    T =.. [F|A],
    !,is_grounded_map(A).
is_grounded(_).
is_grounded_map([]).
is_grounded_map([A|As]) :-
    is_grounded(A),
    is_grounded_map(As).

    


/* (Incl,+Binding,+In,-Out,FV)
 * when Out is the same term as In in which all meta-variables 
 * in Incl are lifted over the context Binding.  a side-effect is
 * to retutn _all_ free meta-variables appearing in In
 */
make_lifted_term(Incl,Binding,T,GT,FV) :- make_lifted_term_(Incl,Binding,T,GT,FV),!.
make_lifted_term_(Incl,Binding,V,GV,[V]) :-
    is_meta_variable(V),
    member(V,Incl),           % NB
    GV =.. [V|Binding].
make_lifted_term_(Incl,Binding,T,GT,FVtotal) :-
    T =.. [V|A],
    is_meta_variable(V),
    member(V,Incl),           % NB
    make_lifted_term_l(Incl,Binding,A,GAs,FVs),
    union(GAs,Binding,NewA),
    union([V],FVs,FVtotal),
    GT =.. [V|NewA].
make_lifted_term_(Incl,Binding,T,GT,FV) :-
    T =.. [F|A],
    make_lifted_term_l(Incl,Binding,A,GA,FV),
    GT =.. [F|GA].

make_lifted_term_l(Incl,_,[],[],[]).
make_lifted_term_l(Incl,Binding,[T|R],[GT|GR],FV) :-
    make_lifted_term_(Incl,Binding,T,GT,FVhead),
    make_lifted_term_l(Incl,Binding,R,GR,FVtail),
    union(FVhead,FVtail,FV).
    



apply_subs_to_pterm_list(S,[],[]).
apply_subs_to_pterm_list(S,[T1|R],[T2|Rs]) :-
    convert([],T1,T1lp),
    apply_subs_to_term(S,T1lp,T2lp),
    convert([],T2,T2lp),
    apply_subs_to_pterm_list(S,R,Rs).


apply_subs_to_rhsinsts(S,[],[]).
apply_subs_to_rhsinsts(S,[Q1-Q2-Q3-Q4|R],[T1-Q2-T3-Q4|Rs]) :-
    convert([],Q1,Q1lp),
    apply_subs_to_term(S,Q1lp,T1lp),
    convert([],T1,T1lp),
    numbervars(Q3,1,_),
    convert([],Q3,Q3lp),
    apply_subs_to_term(S,Q3lp,T3lp),
    convert([],T3,T3lp),
    apply_subs_to_rhsinsts(S,R,Rs).


        % instantiate_hou(+G1,?G2,?G2Vals) the variables quantified in G1
        % can be instantiated with the values of G2Vals to obtain G2.
	% modified to allow for the (arbitrary) instantiation of meta-variables
	% within the goal (via unification)
        %
        % NOTE: We require that ALL variables quantified in G1 are
        % instantiated, thus:
        %      instantiate_hou(x:pnat=>y:pnat=>f(x,y),y:pnat=>f(1,y),[1])
        % will NOT succeed!
instantiate_hou(Subs,G1,G2,Vals) :- instantiate_hou(Subs,G1,G2,[],Vals).
instantiate_hou(Subs,Var:T=>G1,G2,Vars,Vals) :-
    !,instantiate_hou(Subs,G1,G2,[Var|Vars],Vals).
instantiate_hou(Subs,Var1:T1#G1,Var2:T2#G2,Vars,Vals):-
	replace_all(Var2,Var1,G2,GG2),!,
	instantiate_hou(Subs,G1,GG2,Vars,Vals).
instantiate_hou(Subs,G1,G2,Vars,Vals) :-
    /* any (occurrence of a) variable in Vars can be (uniformly) instantiated
     * to some value, Vals.  To do this correctly by unification, we must lift 
     * the meta-variables we replace Vars with over the free variables in the Goal
     */
    length(Vars,N),length(NewVars,N),
    s(G1,NewVars,Vars,G1Alpha),        % replace the free variables in G1 with
                                       % Prolog meta-variables.
    % lift all meta-variables Lfree over context
    freevarsinterm(G2,G2FVs),          % find the context for the lifting
    is_grounded(G1Alpha),
    make_lifted_term(_,G2FVs,G1Alpha,G1AlphaLifted,_),       

    hou_pterms([],Subs,G1AlphaLifted,G2), 
    apply_subs_to_pterm_list(Subs,NewVars,Vals).

gensym_mv_list([],[]).
gensym_mv_list([V|Vs],[Gv|Gvs]) :-
    gensym('M',Gv),
    gensym_mv_list(Vs,Gvs).

remove_elements([],S,S).
remove_elements([E|S],S2,S3) :-
    del_element(E,S2,S4),
    remove_elements(S,S4,S3).


remove_meta_variables([],[]).
remove_meta_variables([H|T],TT) :- is_meta_variable(H),!, remove_meta_variables(T,TT).
remove_meta_variables([H|T],[H|TT]) :- remove_meta_variables(T,TT).


unique_bound_variables(Bound,cv(V,Ty,v)\Body, cv(NewV,Ty,v)\NB) :-
    member(cv(V,Ty,v),Bound),!,
    gensym('bv',NewV),
    alpha_subst(cv(NewV,Ty,v),cv(V,Ty,v),Body,NewBody),
    unique_bound_variables([NewV|Bound],NewBody,NB).
unique_bound_variables(Bound,V\Body, V\NB) :-
    !,
    unique_bound_variables([V|Bound],Body,NB).
unique_bound_variables(Bound,T1 ^ T2, NT1 ^ NT2) :-
    !,unique_bound_variables(Bound,T1,NT1),
    unique_bound_variables(Bound,T2,NT2).

unique_bound_variables(Bound,T1, T1).

/* bound variables in LPnew are legitimate object level variables, and
 * not of the the form 'Wk' or 'Vark' etc, as are used in LP
 * this is almost the same code as unique_bound_variables/3 (oh for
 * higer-order predicates!)
 */
bvs_are_obj_vars(cv(V,Ty,v)\Body, cv(NewV,Ty,v)\NB) :-
    is_meta_variable(V),!,
    gensym('v',NewV),
    alpha_subst(cv(NewV,Ty,v),cv(V,Ty,v),Body,NewBody),
    bvs_are_obj_vars(NewBody,NB).
bvs_are_obj_vars(V\Body, V\NB) :-
    !,
    bvs_are_obj_vars(Body,NB).
bvs_are_obj_vars(T1 ^ T2, NT1 ^ NT2) :-
    !,bvs_are_obj_vars(T1,NT1),
    bvs_are_obj_vars(T2,NT2).

bvs_are_obj_vars(T1, T1).

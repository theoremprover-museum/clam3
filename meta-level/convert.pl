% -*- Prolog -*- 
% @(#)convert.pl	2.7	(93/11/08 10:59:39)
% @(#)Prolog to LProlog conversion


/*
 * Code to convert from Clam/Oyster term syntax of TT to the
 * curried, higher-order representation with explicit types.
 * assumes that the wave-fronts are not empty
 */


/* Note: these operator declarations must be identical to those used
 * in \Prolog.
 */
:- op(164,xfy,\).
:- op(165,yfx,^).    
:- op(150,xfy,--->).   % note NOT ->

is_meta_variable(F) :-
    atom(F),
    atom_codes(F,[K|_]), atom_codes('A',[Ka|_]),
    atom_codes('Z',[Kz|_]),
    K >= Ka, Kz >= K.
    
convert(_,A,B) :-
    var(A), var(B), !, write('domain error convert'),nl,blah.

convert(Bound,A,B) :-
    var(B), 
    convert_annotations(A,Ap),
    convert_(Bound,Ap,B).

convert(Bound,A,B) :-
    var(A), 
    convert_(Bound,Ap,B),
    convert_annotations_back(A,Ap).

% variables/constants of TT
% an object-level variable is always bound in some surrounding context, so 
% make all Bound object-level variables into lp variables (the binder is provided
% from above).
convert_(Bound,Var,cv(Var,term,v)) :-
    atomic(Var),
    \+ var(Var),
    (is_meta_variable(Var); member(Var,Bound)),!.
convert_(Bound,Var,cv(Var,term,c)) :-
    atomic(Var),
    \+ var(Var),!.
% convert only works on ground terms (in the Prolog sense: all Prologvars
% must be explicity mapped into metavariables beforehand
convert_(_,Var,_) :-
    atomic(Var),
    var(Var),
    write('convert domain error'),nl,gdgdgdgdg.

% infix/special ttt's
convert_(Bound,A///[U,V,B], 
    (cv('///',term--->(term--->term--->term)--->term,c)^AA^
                  (cv(U,term,v)\cv(V,term,v)\BB))) :-
    convert_(Bound,A,AA),
    convert_([U,V|Bound],B,BB),!.

convert_(Bound,{C:A\B}, (cv('subset',term--->(term--->term)--->term,c)^AA^
                  (cv(C,term,v)\BB))) :-
    convert_(Bound,A,AA),
    convert_([C|Bound],B,BB),!.
convert_(Bound,C:A=>B, (cv('all',term--->(term--->term)--->term,c)^AA^
                  (cv(C,term,v)\BB))) :-
    convert_(Bound,A,AA),
    convert_([C|Bound],B,BB),!.
/* special case for existentials which have a soft front on
 * the bound variable.
 */
convert_(Bound,'@wave_front@'(soft,_,C):A#B, (cv('some',term--->(term--->term)--->term,c)^AA^
                  (cv(C,term,v)\BB))) :-
    convert_(Bound,A,AA),
    convert_([C|Bound],B,BB),!.
convert_(Bound,C:A#B, (cv('some',term--->(term--->term)--->term,c)^AA^
                  (cv(C,term,v)\BB))) :-
    convert_(Bound,A,AA),
    convert_([C|Bound],B,BB),!.
convert_(Bound,lambda(C,B), (cv('lambda',(term--->term)--->term,c)^
                  (cv(C,term,v)\BB))) :-
    convert_([C|Bound],B,BB),!.
convert_(Bound,rec(C,B), (cv('rec',(term--->term)--->term,c)^
                  (cv(C,term,v)\BB))) :-
    convert_([C|Bound],B,BB),!.

convert_(Bound,A=B in T, (cv('eq',term--->term--->term--->term,c)^Ca^Cb^Ct)) :-
    convert_(Bound,A,Ca), convert_(Bound,B,Cb), convert_(Bound,T,Ct),!.
convert_(Bound,A in T, (cv('in',term--->term--->term,c)^Ca^Ct)) :-
    convert_(Bound,A,Ca), convert_(Bound,T,Ct),!.

convert_(Bound,A#B, (cv('#',term--->term--->term,c)^Ca^Cb)) :-
    convert_(Bound,A,Ca), convert_(Bound,B,Cb),!.
convert_(Bound,A&B, (cv('&',term--->term--->term,c)^Ca^Cb)) :-
    convert_(Bound,A,Ca), convert_(Bound,B,Cb),!.
convert_(Bound,A=>B, (cv('=>',term--->term--->term,c)^Ca^Cb)) :-
    convert_(Bound,A,Ca), convert_(Bound,B,Cb),!.

% meta-variables  (P to LP)
convert_(Bound,Term, LPTerm) :-
    \+ atomic(Term), \+ var(Term),
    Term =.. [F|Rest],
    is_meta_variable(F),
    convert_map(Bound,Rest,LPrest),!,
    make_compose([cv(F,Type,v)|LPrest],LPTerm,Type).

% meta-variables  (LP to P)
convert_(Bound,Term, LPTerm) :-
    \+ atomic(Term), var(Term),
    make_compose([cv(F,Type,v)|LPrest],LPTerm,Type),
    is_meta_variable(F),
    convert_map(Bound,Rest,LPrest),!,
    Term =.. [F|Rest].

%   constant functors (P to LP)
convert_(Bound,Term, LPTerm) :-
    \+ atomic(Term), \+ var(Term),
    Term =.. [F|Rest],
    \+ is_meta_variable(F),
    convert_map(Bound,Rest,LPrest),!,
    make_compose([cv(F,Type,c)|LPrest],LPTerm,Type).

% constant functors (LP to P)
convert_(Bound,Term, LPTerm) :-
    \+ atomic(Term), var(Term),
    make_compose([cv(F,Type,c)|LPrest],LPTerm,Type),
    \+ is_meta_variable(F),
    convert_map(Bound,Rest,LPrest),!,
    Term =.. [F|Rest].

convert_map(_,[],[]).
convert_map(Bound,[T1|Rest],[LPT1|RestLP]) :-
    convert_(Bound,T1,LPT1),
    convert_map(Bound,Rest,RestLP).

make_compose(A,B,T) :- make_compose_(B,A,T),!.
make_compose_(cv(A,B,C),[cv(A,B,C)],term).
make_compose_(A^B, Seq,term--->Type) :-
    make_compose_(A,As,Type), append(As,[B],Seq).

apply_subs_to_sequent(A,B,C) :-
    apply_subs_to_sequent_(A,B,C),!.

apply_subs_to_sequent_(Subs,H==>G,NewH==>NewG) :-
    convert([],G,Glp),
    apply_subs_to_term(Subs,Glp,Glps),
    convert([],NewG,Glps),
    convert_prop_list(Subs,H,NewH).
  
apply_subs_to_sequent_list(Subs,[],[]).
apply_subs_to_sequent_list(Subs,[S|Ss],[SS|SSs]) :-
    apply_subs_to_sequent_(Subs,S,SS),
    apply_subs_to_sequent_list(Subs,Ss,SSs).


convert_prop_list(Subs,[],[]) :- !.
convert_prop_list(Subs,[ih:[R,H]|Hs],[ih:[R,NewH]|NewHs]) :-
    !,convert([],H,HmatLP),
    apply_subs_to_term(Subs,HmatLP,HmatLPSub),
    convert([],NewH,HmatLPSub),
    convert_prop_list(Subs,Hs,NewHs).
convert_prop_list(Subs,[H|Hs],[NewH|NewHs]) :-
    convert([],H,HmatLP),
    apply_subs_to_term(Subs,HmatLP,HmatLPSub),
    convert([],NewH,HmatLPSub),
    convert_prop_list(Subs,Hs,NewHs).

convert_list(_,[],[]).
convert_list(Bound,[T|Ts],[Ct|Cts]) :-
    convert(Bound,T,Ct),
    convert_list(Bound,Ts,Cts).

convert_annotations(B,Bp) :-
    normalize_wave_fronts(B,Bnorm),
    map_annotations(Bnorm,Bp).

convert_annotations_back(B,Bp) :-
    map_annotations_back(Bnorm,Bp),
    un_normalize_wave_fronts(B,Bnorm).

map_annotations(V,V) :- atom(V),!.
map_annotations('@wave_front@'(hard,Dir,Front), Term) :-
    !,Front =.. [F|Args],
    map_annotations_list(Args,MappedArgs),
    wrapped_in_ks(hard,Dir,MappedArgs,Kargs),
    Term =.. [F|Kargs].
map_annotations('@wave_front@'(soft,Dir,Front), Term) :-
    !,
    map_annotations(potential_front(Front), Term).
map_annotations(Termwf, Term) :-
    Termwf =.. [F|Args],
    map_annotations_list(Args,MappedArgs),
    Term =.. [F|MappedArgs].

map_annotations_back(V,V) :- var(V),!.
map_annotations_back(V,V) :- atom(V),!.
map_annotations_back('@wave_front@'(soft,Undirected,Term),potential_front(Front)) :-
    !,map_annotations_back(Term,Front).
map_annotations_back('@wave_var@'(WfTerm), k(_,_,Term)) :-
    !,map_annotations_back(WfTerm,Term).
map_annotations_back('@sink@'(WfTerm), '@sink@'(Term)) :-
    !,map_annotations_back(WfTerm,Term).
map_annotations_back('@wave_front@'(Type,RealDir,Front), Term) :-
    Term =.. [F|Kargs],
    exp_at(Term,[N],k(Type,Dir,_)),
    (Dir == dont_know; Dir = RealDir),!,
    map_annotations_list_back(Args,Kargs),
    Front =.. [F|Args].
map_annotations_back(Termwf, Term) :-
     Term =.. [F|Args],
    map_annotations_list_back(MappedArgs,Args),
   Termwf =.. [F|MappedArgs].

map_annotations_list_back([],[]).
map_annotations_list_back([A|Args],[M|MappedArgs]) :-
    map_annotations_back(A,M),
    map_annotations_list_back(Args,MappedArgs).



wrapped_in_ks(_,_,[],[]).
wrapped_in_ks(Type,Dir,['@wave_var@'(A)|Args],[k(Type,Dir,A)|Kargs]) :-
    !,wrapped_in_ks(Type,Dir,Args,Kargs).
wrapped_in_ks(Type,Dir,[A|Args],[A|Kargs]) :-
    wrapped_in_ks(Type,Dir,Args,Kargs).

map_annotations_list([],[]).
map_annotations_list([A|Args],[M|MappedArgs]) :-
    map_annotations(A,M),
    map_annotations_list(Args,MappedArgs).

normalize_wave_fronts(T,NormT) :-
    rec_split(T,NormT).
rec_split(T,NormT) :-
    split_wave_fronts(T,_,Tnew),
    !,rec_split(Tnew,NormT).
rec_split(T,T).
   

un_normalize_wave_fronts(UnNormT,T) :-
    rec_join(UnNormT,T).
rec_join(UnNormT,T) :-
    join_wave_fronts(T,_,Tnew),
    !,rec_join(UnNormT,Tnew).
rec_join(T,T).
 

contains_meta_variables(T):-
    matrix(_, M, T),
    contains_meta_variables_(M).
contains_meta_variables_(V) :-
    var(V).
contains_meta_variables_(V) :-
    is_meta_variable(V).
contains_meta_variables_(T) :-
    !,T =.. [F|Args],
    (is_meta_variable(F);
    contains_meta_variables_map(Args)).

contains_meta_variables_map([A]) :- contains_meta_variables_(A).
contains_meta_variables_map([A|As]) :-
    contains_meta_variables_(A);
    contains_meta_variables_map(As).

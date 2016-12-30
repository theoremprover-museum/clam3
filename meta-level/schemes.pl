/*
 * This file contains all the code needed to make different induction
 * schemes work.
 * The main workhorses are scheme/5 (which is the specification of the
 * different schemes available), and is_recursive/5, which knows about
 * recursion equations etc.
 * There should be a scheme/5 clause for every induction scheme the
 * system knows about. 
 * 
 */

        % scheme(+Scheme, +Var, +Sequent, ?BaseSequents, ?StepSequents):
        % Given a Scheme (for induction) and a Var (to induce on),
        % scheme/5 maps a Sequent to a list of BaseSequents and a list of
        % StepSequents that will be produced by induction on Var.
        %
        % There should be a scheme/5 clause for every induction scheme
        % we want to be able to use in the system.
        %
        % Notice that this representation of induction schemes
        % distinguishes between schemes on the basis of the induction
        % term (the wave-fronts) it introduces. These wave fronts are
        % used to "index" the induction schemes. Unfortunately, this is
        % not quite good enough: different induction schemes can
        % introduce the same wave-front (see e.g. the two distinct
        % inductions below both with the wave-front times(_,_)). Thus,
        % this identification of induction schemes should at some point
        % be enhanced.
        %
        % Notice that apart from just specifying the logical structure
        % of the inductions (basesequents and stepsequents), we also
        % specify some of the heuristic story (namely we introduce the
        % wave-fronts). 
        % 
        % Need dynamic declaration for execution of scheme/2.
        %
        % The code for scheme/5 is so repetitive and almost mechanical
        % between the different induction schemes that maybe we should
        % sometimes think of a nicer notation for all of this. (Higher
        % order unification would help as a starter...).
:- dynamic( scheme/5 ).
:- dynamic( scheme/1 ).
scheme([s(x),y::z]).
scheme([s(NewNat),NewHead::NewTail],
       [Var1:pnat, Var2:T list],
       H==>G,
       [HBase1==>GBase1,
        HBase2==>GBase2],
       [[NewHead:T,
         NewTail:T list,
         NewNat:pnat,
         NewH:ih(IndHyp)|HBase]==>GStep]) :-
    matrix(Vs,WGm,G), Gm=WGm, % **** USED TO BE wave_fronts(Gm,_,WGm),
    append(H, Vs, Bindings),
    append([Var2:T list, Var1:pnat], H, HBase),
    hfree([NewHead,NewTail,NewNat, NewH],Bindings),
    del_element(Var1:pnat,Vs,VsDelVar1),
    del_element(Var2:T list,VsDelVar1,OVsStep),
    OVsBase = OVsStep,
    append(HBase,[NewHead:T list],HBase1),    append(HBase,[NewHead:pnat],  HBase2),
    wave_fronts(s(NewNat),[[]-[[1]]/[hard,out]],StepTerm1),
    wave_fronts(NewHead::NewTail,[[]-[[2]]/[hard,out]],StepTerm2),
    mark_sinks(OVsStep,Gm,GmS),
    wave_fronts(BGm,_,Gm),
    replace_all(Var2,nil,BGm,GBase_1), 
    %%% replace_all(Var2, NewHead, GBase_1,GBase_11),   
    matrix(OVsBase,GBase_1,GBase1),
    replace_all(Var1,0,BGm,GBase_2),            
    %%% replace_all(Var2, NewHead, GBase_2,GBase_22),   
    matrix(OVsBase,GBase_2,GBase2),
    replace_all(Var2,NewTail,Gm,IndHyp_1), 
    replace_all(Var1,NewNat,IndHyp_1,IndHyp_2),     matrix(OVsStep,IndHyp_2,IndHyp),  
    replace_all(Var1,StepTerm1,GmS,GStep_1), 
    replace_all(Var2,StepTerm2,GStep_1,GStep_2),
    mark_potential_waves(GStep_2,GStep_3),
    matrix(OVsStep,GStep_3,GStep).

        % primitive recursion on pnats:
scheme([s(x)]).
scheme([s(Var)],
       [Var:pnat],
       H==>G,
       [[Var:pnat|H]==>GBase],
       [[Var:pnat, IndHypVar:ih(IndHyp)|H]==>GStep]) :-
          % hack to avoid confusion between s(_) and s(s(_)):
    (var(Var);atomic(Var)),
    matrix(Vs,WGm,G),    Gm=WGm, % **** USED TO BE wave_fronts( Gm, _, WGm ),
    del_element(Var:pnat,Vs,OVs),
    append(Vs,H,Bindings),
    hfree([IndHypVar],Bindings),
    wave_fronts(s(Var),[[]-[[1]]/[hard,out]], StepTerm),
    mark_sinks(OVs,Gm,GmS),
    wave_fronts(GmB,_,Gm),
    replace_all(Var,0,GmB,GBase1),               matrix(OVs,GBase1,GBase),
    replace_all(Var,Var,GmB,IndHyp1),            matrix(OVs,IndHyp1,IndHyp),
    replace_all(Var,StepTerm,GmS,GStep1),       
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).

        % two step induction on pnats:
scheme([s(s(x))]).
scheme([s(s(Var))],
       [Var:pnat],
       H==>G,
       [[Var:pnat|H]==>GBase1, [Var:pnat|H]==>GBase2],
       [[Var:pnat, IndHypVar:ih(IndHyp)|H]==>GStep]) :-
          % hack to avoid confusion between s(_) and s(s(_)):
    (var(Var);atomic(Var)),
    matrix(Vs,WGm,G),    Gm=WGm, % **** USED TO BE wave_fronts( Gm, _, WGm ),
    del_element(Var:pnat,Vs,OVs),
    append(Vs,H,Bindings),
    hfree([IndHypVar],Bindings),
    wave_fronts(s(s(Var)),[[]-[[1,1]]/[hard,out]], StepTerm),
    mark_sinks(OVs,Gm,GmS),
    wave_fronts(GmB,_,Gm),
    replace_all(Var,0,GmB,GmB1),                 matrix(OVs,GmB1,GBase1),
    replace_all(Var,s(0),GmB,GmB2),              matrix(OVs,GmB2,GBase2),
    replace_all(Var,Var,GmB,IndHyp1),            matrix(OVs,IndHyp1,IndHyp),
    replace_all(Var,StepTerm,GmS,GStep1),       
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).

        % four step recursion on pnats:
scheme([s(s(s(s(x))))]).
scheme([s(s(s(s(Var))))],
       [Var:pnat],
       H==>G,
       [[Var:pnat|H]==>GBase1,
        [Var:pnat|H]==>GBase2,
        [Var:pnat|H]==>GBase3,
        [Var:pnat|H]==>GBase4],
       [[Var:pnat, NewH:ih(IndHyp)|H]==>GStep]) :-
    matrix(Vs,WGm,G), Gm=WGm, % **** USED TO BE wave_fronts(Gm,_,WGm),
    del_element(Var:pnat,Vs,OVs),
    append(H,Vs,VarBase),
    hfree([NewH],VarBase),
    wave_fronts(s(s(s(s(Var)))),[[]-[[1,1,1,1]]/[hard,out]],StepTerm),
    wave_fronts(GmB, _, Gm),
    replace_all(Var,0,GmB,GmB1),    
    matrix(OVs,GmB1,GBase1),            
    replace_all(Var,s(0),GmB,GmB2),    
    matrix(OVs,GmB2,GBase2),           
    replace_all(Var,s(s(0)),GmB,GmB3),    
    matrix(OVs,GmB3,GBase3),           
    replace_all(Var,s(s(s(0))),GmB,GmB4),    
    matrix(OVs,GmB4,GBase4),           
    matrix(OVs,GmB,IndHyp),  
    mark_sinks(OVs,Gm,GmS),
    replace_all(Var,StepTerm,GmS,GStep1), 
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).

        % primitive recursion on lists:
scheme([x::y]).
scheme([NewHead::Var],
       [Var:T list],
       H==>G,
       [[Var:T list|H]==>GBase],
       [[NewHead:T, Var:T list, NewH:ih(IndHyp)|H]==>GStep]) :-
    matrix(Vs,WGm,G), Gm=WGm, % **** USED TO BE wave_fronts(Gm,_,WGm),
    del_element(Var:T list,Vs,OVs),
    append(H,Vs,VarBase),
    hfree([NewHead, NewH],VarBase),
    wave_fronts(NewHead::Var,[[]-[[2]]/[hard,out]],StepTerm),
    wave_fronts(GmB, _, Gm),
    replace_all(Var,nil,GmB,GBase1),    
    matrix(OVs,GBase1,GBase),            
    matrix(OVs,GmB,IndHyp),  
    mark_sinks(OVs,Gm,GmS),
    replace_all(Var,StepTerm,GmS,GStep1), 
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).

        % two step recursion on lists:
scheme([x::y::z]).
scheme([Head1::Head2::Var],
       [Var:T list],
       H==>G,
       [[Var:T list|H]==>GBase1,
        [Head1:T, Var:T list|H]==>GBase2],
       [[Head1:T, Head2:T, Var:T list, NewH:ih(IndHyp)|H]==>GStep]) :-
    matrix(Vs,WGm,G), Gm=WGm, % **** USED TO BE wave_fronts(Gm,_,WGm),
    del_element(Var:T list,Vs,OVs),
    append(H,Vs,VarBase),
    hfree([Head1, Head2, NewH],VarBase),
    wave_fronts(Head1::Head2::Var,[[]-[[2,2]]/[hard,out]],StepTerm),
    wave_fronts(GmB, _, Gm),
    replace_all(Var,nil,GmB,GmBnil),    
    matrix(OVs,GmBnil,GBase1),            
    replace_all(Var,Head1::nil,GmB,GmBsingle),    
    matrix(OVs,GmBsingle,GBase2),            
    matrix(OVs,GmB,IndHyp),  
    mark_sinks(OVs,Gm,GmS),
    replace_all(Var,StepTerm,GmS,GStep1), 
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).

        % four step recursion on lists:
scheme([v::w::x::y::z]).
scheme([Head1::Head2::Head3::Head4::Var],
       [Var:T list],
       H==>G,
       [[Var:T list|H]==>GBase1,
        [Head1:T, Var:T list|H]==>GBase2,
        [Head1:T, Head2:T, Var:T list|H]==>GBase3,
        [Head1:T, Head2:T, Head3:T, Var:T list|H]==>GBase4],
       [[Head1:T, Head2:T, Head3:T, Head4:T, Var:T list, NewH:ih(IndHyp)|H]==>GStep]) :-
    matrix(Vs,WGm,G), Gm=WGm, % **** USED TO BE wave_fronts(Gm,_,WGm),
    del_element(Var:T list,Vs,OVs),
    append(H,Vs,VarBase),
    hfree([Head1, Head2, Head3, Head4, NewH],VarBase),
    wave_fronts(Head1::Head2::Head3::Head4::Var,[[]-[[2,2,2,2]]/[hard,out]],StepTerm),
    wave_fronts(GmB, _, Gm),
    replace_all(Var,nil,GmB,GmB1),    
    matrix(OVs,GmB1,GBase1),            
    replace_all(Var,Head1::nil,GmB,GmB2),    
    matrix(OVs,GmB2,GBase2),           
    replace_all(Var,Head1::Head2::nil,GmB,GmB3),    
    matrix(OVs,GmB3,GBase3),           
    replace_all(Var,Head1::Head2::Head3::nil,GmB,GmB4),    
    matrix(OVs,GmB4,GBase4),           
    matrix(OVs,GmB,IndHyp),  
    mark_sinks(OVs,Gm,GmS),
    replace_all(Var,StepTerm,GmS,GStep1), 
    mark_potential_waves(GStep1,GStep2),
    matrix(OVs,GStep2,GStep).






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                               %%
%%  Index to the corpus of example theorems      %%
%%  currently planned and executed by the        %%
%%  Clam-Oyster automated proof system.          %%
%%						 %%
%%  example/3 specifies the type and name of     %%
%%  each example. 				 %%
%%						 %%
%%						 %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%				   %%
%%	 Verification examples     %%
%%				   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


/*
 *
 *  arith
 *
 */

example(arith,   assp	        ,try).
example(arith,   assm	        ,try).
example(arith,   comm	        ,try).
example(arith,   commtwo	,try).
example(arith,   plus1right	,try).
example(arith,   plus2right	,try).
example(arith,   times1right	,try).
example(arith,   times2right	,try).
example(arith,   commthree	,try).
example(arith,   binom_one	,try).
example(arith,   comp	        ,try).
example(arith,   comp2	        ,try).
example(arith,   dist	        ,try).
example(arith,   disttwo	,try).
example(arith,   minmax	        ,try).        % requires simultaneous induction
example(arith,   lesss	        ,try).
example(arith,   zeroplus	,try).
example(arith,   zerotimes	,try).
example(arith,   zerotimes1	,try).
example(arith,   zerotimes2	,try). 		
example(arith,   geqnotlessp	,try).        % requires simultaneous induction
example(arith,   lesstrich	,skip).    % simult induc: base-case failure
example(arith,   plusgeq	,try).
example(arith,   plusgeq2	,try).
example(arith,   evendouble	,try).
example(arith,   halfdouble	,try).
example(arith,   doubletimes1	,try).
example(arith,   doubletimes2	,try).
example(arith,   expplus	,try).
example(arith,   exptimes	,try).
example(arith,   evenodd1	,try).
example(arith,   evenodd2	,try).
example(arith,   lesstrans1	,try).	% requires simultaneous induction
example(arith,   lesstrans2	,try).	% requires simultaneous induction
example(arith,   lesstrans3	,try).	% requires simultaneous induction
example(arith,   notlesstrans	,try).	% requires simultaneous induction
example(arith,   notlesstrans2	,try).	% requires simultaneous induction
example(arith,   notlesstrans3	,try).	% requires simultaneous induction
example(arith,   notleqreflex	,try).
example(arith,   lesseq	        ,try).	% requires simultaneous induction
example(arith,   leqtrans	,try).	% requires simultaneous induction
example(arith,   greatertrans	,try).	% requires simultaneous induction
example(arith,   greatercons	,try).
example(arith,   leqdupl	,try).    % requires simultaneous induction
example(arith,   leqdouble	,try).
example(arith,   leqhalf	,try).
example(arith,   leqhalfdouble	,try).	
example(arith,   halfpnat	,try).
example(arith,   greaterplus	,try).    % requires simultaneous induction
example(arith,   greaterplus2	,try).
example(arith,   greaterplus3	,needs_normalize).    % requires normalize
example(arith,   greatertimes	,skip). % simult induct: requires greaterplus 
example(arith,   greaters	,try).
example(arith,   greaters2	,try).	 % requires simultaneous induction
example(arith,   greatercancel	,skip). % infinite nesting of inductions
example(arith,   grsqsuc	,skip). % missed cancellation (?)
example(arith,   geqhalf	,try).
example(arith,   geqdouble	,try).
example(arith,   geqdoublehalf	,try).
example(arith,   evenp	        ,try).
example(arith,   evenm	        ,try).
example(arith,   prodl	        ,try).
example(arith,   prodlwave	,needs_normalize).	% requires normalize
example(arith,   minus_pred	,try).
example(arith,	 minus_succ	,try).
example(arith,   minus_plus	,try).


/*
 *
 *  lists
 *
 */


example(lists,   litapp	        ,try).
example(lists,   apprev	        ,try).
example(lists,   assapp	        ,try).
example(lists,   comapp	        ,try).
example(lists,   lenrev	        ,try).
example(lists,   lenapp	        ,try).
example(lists,   lensum	        ,try).
example(lists,   memapp1	,try).
example(lists,   memapp2	,try).
example(lists,   memapp3	,try).
example(lists,   app1right	,try).
example(lists,   memrev	        ,try).		
example(lists,   revrev	        ,try).
example(lists,   revqrev	,try).
example(lists,   tailrev	,try).
example(lists,   tailrev2	,try).
example(lists,   singlerev	,try).
example(lists,   nthmem	        ,try).     % requires simultaneous induction
example(lists,   nthapp	        ,try).	
example(lista,   minmaxgeq	,try).    % requires simultaneous induction
example(lists,   mapcarapp	,try).
example(lists,   lenmapcar	,try).
example(lists,   revmapcar	,try).
example(lists,   subsetcons	,skip).  % case-split required within sym-eval
example(lists,   lensort	,try).
example(lists,   subsetunion	,try).
example(lists,   subsetintersect,try).
example(lists,   memunion1	,try).
example(lists,   memunion2	,try).
example(lists,   memintersect	,try).
example(lists,   leqnth	        ,try).
example(lists,	 memins	        ,try).
example(lists,   meminsert1	,needs_normalize).    % requires normalize
example(lists,   meminsert2	,needs_normalize).    % requires normalize
example(lists,   memsort1	,try).
example(lists,   memsort2	,try).
example(lists,   countsort	,try).
example(lists,   rotlen	        ,try).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%				   %%
%%	 Synthesis examples        %%
%%				   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


/*
 *  arith
 */

example(arith,   factors	,try).

/*
 *  lists
 */

example(lists,   tcons	        ,try).

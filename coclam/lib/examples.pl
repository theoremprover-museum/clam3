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

%% Lemma discovery examples
%% 
%%       calculation
%%
example(lemma,   doubleplus        ,_).    % t1
example(lemma,   lenapp            ,_).    % t2
example(lemma,   lenplus           ,_).    % t3
example(lemma,   lendouble         ,_).    % t4
example(lemma,   lenrev            ,_).    % t5
example(lemma,   lenrevapp         ,_).    % t6
example(lemma,   lenqrevapp        ,_).    % t7
example(lemma,   nthnth1           ,_).    % t8:
example(lemma,   nthnth2           ,_).    % t9:
example(lemma,   revrev            ,_).    % t10
example(lemma,   revapp1           ,_).    % t11
example(lemma,   revqrev           ,_).    % t12
example(lemma,   halfplus1         ,_).    % t13

%%
%%       speculation
%%
example(lemma,   ordsort           ,skip). % t14: failure: prf of lemma
example(lemma,   plusxx            ,_).    % t15
example(lemma,   evenplus1         ,_).    % t16
example(lemma,   revapp4           ,_).    % t17
example(lemma,   revapp2           ,_).    % t18
example(lemma,   revapp3           ,_).    % t19
example(lemma,   evenlenapp1       ,_).    % t20
example(lemma,   rotlenapp         ,_).    % t21

%%
%%      induction revision
%%
%%
example(lemma,   evenlenapp2       ,_).    % t22
example(lemma,   halflenapp1       ,_).    % t23
example(lemma,   evenplus2         ,_).    % t24
example(lemma,   evenlenapp3       ,_).    % t25
example(lemma,   halfplus2         ,_).    % t26

%% Generalisation examples
%%
%%      sink speculation
%%
example(lemma,   revqrevnil1       ,_).    % t27
example(lemma,   revflatqrev       ,_).    % t28
example(lemma,   revqrevnil2       ,_).    % t29
example(lemma,   revrevnil1        ,_).    % t30
example(lemma,   qrevqrevnil1      ,_).    % t31
example(lemma,   rotlen            ,_).    % t32
example(lemma,   facqfac           ,_).    % t33
example(lemma,   timesmult         ,_).    % t34
example(lemma,   expqexp           ,_).    % t35
example(lemma,   facout            ,_).    % 


%% Casesplit & lemma discovery examples
%%
%%
example(lemma, memapp1             ,_).    % t36
example(lemma, memapp2             ,_).    % t37
example(lemma, memapp3             ,_).    % t38
example(lemma, nthmem              ,_).    % t39
example(lemma, subsetunion         ,_).    % t40
example(lemma, subsetintersect     ,_).    % t41
example(lemma, memunion1           ,_).    % t42
example(lemma, memunion2           ,_).    % t43
example(lemma, memintersect        ,_).    % t44
example(lemma, memins              ,_).    % t45
example(lemma, meminsert1          ,_).    % t46
example(lemma, meminsert2          ,_).    % t47
example(lemma, memsort1            ,_).    % t48
example(lemma, lensort             ,_).    % t49
example(lemma, countsort           ,_).    % t50








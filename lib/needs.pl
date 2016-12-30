/*
 * This file should contain all theneeds/2 clauses to record
 * dependencies between logical objects such as definitions, theorems,
 * lemma's etc. 
 *
 */

% Declare dynamic so that users can modify this database with their own
% clauses, using assert/retract.
:- dynamic needs/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% nm-bit Multiplier
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(multVer), [def(word2nat),
                     def(multlist),
                     wave(caddVerMult),
                     wave(distTimesPlus),
                     wave(assm),
                     wave(assTimes1),
                     wave(assTimes2),
                     wave(appMultZero),
                     wave(assAppCons),
                     wave(timesTwo),
                     wave(cnc_s),
                     red(appNil),
                     red(timesZero),
                     red(plusZero),
                     red(timesOne),
                     red(timesZero)]).

needs(def(word2nat), [def(plus),def(times),def(bitval),def(exptwo),
                      def(length)]).
needs(def(bitval),     [def(bool_eq),def(true),def(false)]).
needs(def(val),    [def(plus),def(times),def(exp),def(bitval),def(vec)]).
needs(def(boolVal),  [def(pnat_eq),def(minus),def(true),def(false),def(exp),
                      def(arb)]).
needs(def(multlist), [def(app),def(multOne),def(zeroes),def(length),def(cadd)]).
needs(def(cadd), [def(add),def(hd),def(tl)]).
needs(def(add), [def(faCarry),def(faSum),def(hd),def(tl)]).
needs(def(multOne), [def(and)]).
needs(def(zeroes), [def(false)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% facout example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(facout),      [def(fac),def(out),wave(assm)]).
needs(def(out),         [def(times)]).
needs(thm(facoutgen),   [def(fac),def(out)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% partition example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(partition),    [def(partition),def(app),def(evenel),def(oddel),
                          wave(appatend)]).
needs(def(partition),    [def(odd),def(even),def(atend)]).
needs(def(evenel),       [def(even)]).
needs(def(oddel),        [def(odd)]).

needs(thm(partitiongen1), [def(partition),def(app),def(evenel),def(oddel),
                           wave(appatend)]).
needs(thm(partitiongen2), [def(partition),def(app),def(evenel),def(oddel),
                           red(app1right)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% partitionfilter
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(partitionfilter),    [def(partition),def(app),def(lam),
                                def(filter),red(app1right),wave(appatend)]).
needs(def(partition),          [def(odd),def(even),def(atend)]).
needs(def(filter),             [def(ap)]).
needs(thm(partitionfiltergen),    [def(partition),def(app),def(lam),
                                   def(filter),wave(appatend)]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% splilist example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(splitlist),    [def(lam),def(split),def(map),
                          def(reduce),def(app),
                          wave(mapapp),wave(cnc_app),wave(appatend)]).

needs(thm(splitlistgen), [def(lam),def(split),def(map),
                          def(reduce),def(app),
                          wave(mapapp),wave(cnc_app),wave(appatend)]).

needs(thm(mapapp),       [def(map),def(app)]).
needs(thm(cnc_app),      [def(app)]).
needs(thm(appatend),     [def(app),def(atend)]).

needs(def(split),        [def(greater),def(atend)]).
needs(def(map),          [def(ap)]).
needs(def(reduce),       [def(ap)]).
needs(def(greater),      [def(less)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% sumprod example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(sumprod),             [def(sp),def(sum),def(prod),
                                 red(times1right),
                                 red(times2right),
                                 wave(assp),wave(assm)]).
needs(thm(sumprodgen),          [def(sp),def(sum),def(prod),
                                 red(times1right),
                                 red(times2right),
                                 wave(assp),wave(assm)]).
needs(def(sp),                  [def(plus),def(times)]).
needs(def(sum),                 [def(plus)]).
needs(def(prod),                [def(times)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tsumtprodfoldl example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(tsumtprodfoldl),      [def(foldl),def(tsum),def(tprod),
                                 red(times1right),
                                 red(times2right),
                                 wave(assp),wave(assm)]).
needs(thm(tsumtprodfoldlgen),   [def(sp),def(foldl),def(tsum),def(tprod),
                                 red(times1right),
                                 red(times2right),
                                 wave(assp),wave(assm)]).
needs(def(tsum),                 [def(plus)]).
needs(def(tprod),                [def(times)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% spfoldl example
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(spfoldl),             [def(sp),def(foldl),def(sum),def(prod),
                                 wave(assp),wave(assm)]).
needs(thm(spfoldlgen),          [def(sp),def(foldl),def(sum),def(prod),
                                 wave(assp),wave(assm)]).
needs(def(sum),                 [def(plus)]).
needs(def(prod),                [def(times)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(times),       	[def(plus)]).
needs(def(mult),                [def(plus)]).
needs(def(divides),     	[def(times)]).
needs(def(minus),       	[def(pred)]).
needs(def(prime),       	[def(posint),def(divides)]).
needs(def(prodl),       	[def(times)]).
needs(def(even),        	[synth(even),def(true)]).
needs(def(odd),         	[synth(odd),def(true)]).
needs(def(half),        	[synth(half)]).
needs(def(fac),         	[def(times)]).
needs(def(qfac),         	[def(times)]).
needs(def(fib),                 [def(plus)]).
needs(thm(qplus1right),         [def(qplus)]).
needs(thm(assp),        	[def(plus)]).
needs(thm(assm),        	[def(times)]).
needs(thm(comm),        	[def(times),wave(cnc_s),wave(cnc_plus)]).
needs(thm(commtwo),     	[def(times)]). 
needs(thm(plus1right),  	[def(plus)]).
needs(thm(plus2right),  	[def(plus)]).
needs(thm(times1right), 	[def(times)]).
needs(thm(times2right), 	[def(times)]).
needs(thm(commthree),   	[def(times),wave(disttwo),wave(times2right)]).
needs(thm(binom_one),   	[def(minus),def(plus),def(binom),
				  red(plus1right),red(plus2right)] ).
needs(thm(comp),        	[def(plus),wave(cnc_s)]).
needs(thm(comp2),       	[def(plus)]).
needs(thm(dist),        	[def(plus),def(times)]).
needs(thm(disttwo),     	[def(plus),def(times)]).
needs(synth(even),      	[scheme(twos)]).
needs(synth(odd),       	[scheme(twos)]).
needs(synth(half),      	[scheme(twos)]).
needs(synth(plus),      	[]). % previously [scheme(prim)]).
needs(def(leq),         	[def(true)]).
needs(def(geq),         	[def(true)]).
needs(thm(minmax),      	[def(min),def(max),def(leq),scheme(pairs)]).
needs(thm(lesss),       	[def(less)]).
needs(thm(zeroplus),    	[def(plus)]).
needs(thm(zerotimes),   	[def(times),wave(zeroplus)]).
needs(thm(zerotimes1),  	[def(times)]).
needs(thm(zerotimes2),  	[def(times)]).
needs(thm(geqnotlessp), 	[def(geq),def(less),scheme(pairs)]).
needs(thm(lesstrich),   	[def(less),def(greater),wave(cnc_s),
                                 scheme(pairs)]).
needs(thm(plusgeq),     	[def(plus),def(geq)]).
needs(thm(plusgeq2),    	[def(plus),def(geq),wave(plus2right)]).
needs(thm(evendouble),  	[def(even),def(double)]).
needs(thm(halfdouble),  	[def(half),def(double)]).
needs(thm(halflenapp1),         [def(half),def(length),def(even),
                                 def(app),wave(ssid)]).
needs(thm(doublehalf),  	[def(half),def(even),def(double),wave(cnc_s)]).
needs(thm(doubleplus),          [def(double),def(plus)]).
needs(thm(doubletimes1),	[def(double),def(times),
				  wave(times2right),wave(cnc_s)]).
needs(thm(doubletimes2),	[def(double),def(times),wave(cnc_s)]).
needs(def(exp),         	[def(times)]).
needs(def(qexp),         	[def(times)]).
needs(thm(expplus),     	[def(exp),def(plus),wave(disttwo),wave(dist),
				  scheme(plusind), red(times1right),red(times2right),
				  red(plus1right)]).
needs(thm(exptimes),    	[def(exp),def(times),scheme(plusind),
				  wave(expplus),wave(dist)]).

needs(thm(facqfac),             [def(fac),def(qfac),wave(assm)]).
needs(thm(fibqfib),             [def(fib),def(qfib),wave(assp)]).
needs(thm(timesmult),           [def(times),def(mult),wave(assp)]).
needs(thm(expqexp),             [def(exp),def(qexp),wave(assm)]).

needs(thm(evenodd1),    	[def(even),def(odd)]).
needs(thm(evenodd2),    	[def(even),def(odd)]).
needs(thm(lesstrans1),  	[def(less),scheme(pairs)]).
needs(thm(lesstrans2),  	[def(less),def(leq),scheme(pairs)]).
needs(thm(lesstrans3),  	[def(less),scheme(pairs)]).
needs(thm(notlesstrans),	[def(less),def(leq),scheme(pairs)]).
needs(thm(notlesstrans2),	[def(less),def(leq),scheme(pairs)]).
needs(thm(notlesstrans3),	[def(leq),scheme(pairs)]).
needs(thm(notleqreflex),	[def(leq)]).
needs(thm(lesseq),      	[def(less),def(leq),wave(cnc_s),
                                 scheme(pairs)]).
needs(thm(leqtrans),    	[def(leq),scheme(pairs)]).
needs(thm(greatertrans),	[def(greater),scheme(pairs)]).
needs(thm(greatercons), 	[def(greater),def(length)]).
needs(thm(leqdupl),     	[def(leq),scheme(pairs)]).
needs(thm(leqdouble),   	[def(leq),def(double)]).
needs(thm(leqhalf),     	[def(leq),def(half)]).
needs(thm(leqhalfdouble),   	[def(leq),def(half),def(double)]).
needs(thm(halfplus1),		[def(plus),def(half),wave(cnc_s),wave(cnc_half)]).
needs(thm(halfplus),		[def(plus),def(half),wave(cnc_s),
                                 wave(cnc_half)]).
needs(thm(halfplus2),           [def(plus),def(half),wave(cnc_s),wave(cnc_half),wave(ssid)]).
needs(thm(plusxx),              [def(plus),wave(ssid),wave(cnc_s)]).
needs(thm(greaterplus), 	[def(greater),def(plus),scheme(pairs)]).
needs(thm(greaterplus2),	[def(greater),def(plus)]).
needs(thm(greaterplus3), 	[def(greater),def(plus)]). % mthd(normalize/_) 
needs(thm(greatertimes),	[def(greater),def(times),
				 mthd(apply_lemma/_),thm(greaterplus),
                                 scheme(pairs)]).
needs(thm(greaters),    	[def(greater)]).
needs(thm(greaters2),    	[def(greater),scheme(pairs)]).
needs(thm(greatercancel),	[def(greater),def(times)]).
needs(thm(grsqsuc),		[def(greater),def(times)]).
needs(thm(geqhalf),		[def(geq),def(half)]).
needs(thm(geqdouble),		[def(geq),def(double)]).
needs(thm(geqdoublehalf),	[def(geq),def(double),def(half)]).
needs(thm(cnc_pred),    	[def(pred)]).
needs(thm(minus_pred),   	[def(minus),wave(cnc_pred)]).
needs(thm(minus_succ),   	[def(minus),wave(cnc_pred)]).
needs(thm(minus_plus), 		[def(plus),def(minus),wave(cnc_pred)]).
				  % Previously wave(minus_succ)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% primefac stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(evenleven),           [def(app),def(length),def(even),def(evenl)]).
needs(thm(evenapp),             [def(app),def(length),def(even)]).
needs(thm(evenlen),             [def(app),def(length),def(even)]).
needs(thm(evenlenapp1),         [def(app),def(length),def(even)]).
needs(thm(evenlenapp2),         [def(app),def(length),def(even),wave(ssid)]).
needs(thm(evenlenapp3),         [def(app),def(plus),def(length),def(even),wave(ssid)]).
needs(thm(evenoddhalf),         [def(even),def(odd),def(half)]).
needs(thm(evenplus1),           [def(even),def(plus)]). 
needs(thm(evenplus2),           [def(even),def(plus),wave(ssid)]).
needs(thm(evenp),       	[def(even),def(plus),scheme(twos)]).
needs(thm(evenm),       	[def(even),def(times)]).
needs(thm(evenm1),       	[def(even),def(times)]).
needs(thm(evenm2),       	[def(even),def(times)]).
needs(thm(evenm3),       	[def(even),def(times)]).
needs(thm(prodl),       	[def(prodl),def(pnatapp),def(times),
				 mthd(apply_lemma/_),thm(assm)]).
needs(thm(prodlwave),   	[def(prodl),def(pnatapp),def(times),
				 mthd(apply_lemma/_), thm(assm)]). % mthd(normalize/_)
needs(lemma(identrm),   	[def(times)]).
needs(lemma(not0lm),    	[def(times)]).
needs(lemma(not0rm),    	[def(times)]).

% NOTE: Can not prove primefac (version 1.4 or 1.5.1). I (AndrewS)
% am working on this - it requires a lot of middle-out stuff to be
% properly sorted: checking types of solution terms are sensible
% controlling symbolic evaluation, conditional fertilization ....
% Probably proper control of potential wave-fronts etc as well
%
%
%needs(thm(primefac),   [def(prime),def(prodl),scheme(primec),wave(prodlwave),
%                         red(identrm),lemma(not0lm),lemma(not0rm)]).
%
% NOTE: Existential rippling synthesizes primefac in the context of
% constructor style induction (see factors for more detail).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% list stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(rev),         	[def(app)]).
needs(thm(litapp),      	[def(app),def(lit)]).
needs(thm(apprev),      	[def(app),def(rev)]).
needs(thm(assapp),      	[def(app)]).
needs(thm(comapp),      	[def(app),def(length)]).
needs(thm(lenrev),      	[def(length),def(rev)]).
needs(thm(lenapp),      	[def(length),def(app)]).
needs(thm(lensum),      	[def(length),def(app),def(plus)]).
needs(thm(lenplus),      	[def(length),def(app),def(plus)]).
needs(thm(lendouble),           [def(length),def(double),def(app)]).
needs(thm(lenrev),              [def(rev),def(length)]).
needs(thm(lenrevapp),           [def(rev),def(length),def(app),def(plus)]).
needs(thm(lenqrevapp),           [def(qrev),def(length),def(plus)]).
needs(def(member),      	[def(true)]).
needs(thm(memapp1),             [def(member),def(app)]).
needs(thm(memapp2),     	[def(member),def(app)]).
needs(thm(memapp3),     	[def(member),def(app)]).
needs(thm(app1right),   	[def(app)]).
needs(thm(memrev),      	[def(member),def(rev),wave(memapp3),
                                 wave(disjeq)]).
needs(thm(revrev),      	[def(rev)]). 
needs(thm(revqrev),     	[def(rev),def(qrev)]).
needs(thm(revqrevnil1),     	[def(rev),def(qrev),wave(assapp)]).
needs(thm(revqrevnil2),     	[def(rev),def(qrev),wave(assconsapp),wave(tailrev1)]).
needs(thm(revqrevnil3),         [def(perm),def(rev),def(qrev),wave(assapp)]).
needs(thm(revqrevnil4),         [def(rev),def(qrev),wave(assapp),wave(tailrev1),wave(assconsapp)]).
needs(thm(revqrevredapp),       [def(rev),def(qrev),def(reduce),def(ap),def(lam),
                                 wave(assapp)]).
needs(thm(revqrevredatend),     [def(rev),def(qrev),def(reduce),def(atend),def(ap),def(lam),
                                 wave(appatend)]).
needs(thm(revrevnil1),     	[def(rev),def(app)]). % ,wave(assconsapp)]). 
needs(def(perm),                [def(del),def(member)]).
needs(thm(qrevqrevnil1),        [def(qrev)]).
needs(thm(qrevqrevnil2),        [def(app),def(qrev),wave(assapp)]).
needs(thm(revqrev2),     	[def(rev),def(qrev),wave(cnc_cons)]).
needs(thm(revqrevapp1),         [def(rev),def(qrev),wave(cnc_cons)]).
needs(thm(revqrevapp2),         [def(rev),def(qrev),wave(cnc_cons)]).
needs(thm(lenqrevnil),          [def(length),def(qrev),wave(assapp)]).
needs(thm(qrevqrevnil),         [def(qrev),wave(assapp)]).
needs(thm(revapp1),             [def(rev)]).
needs(thm(revapp2),             [def(rev)]).
needs(thm(revapp3),             [def(rev)]).
needs(thm(revapp4),             [def(rev)]). %,wave(cnc_cons),wave(cnc_cons),wave(cnc_right_app)]).
needs(thm(revflatqrev),         [def(rev_flatten),def(qrev_flatten),wave(assapp)]).
needs(def(rev_flatten),         [def(app)]).
needs(thm(tailrev1),     	[def(rev),def(app)]).
needs(thm(tailrev2),    	[def(rev),def(app)]).
needs(thm(tailrev3),    	[def(rev),def(app),wave(cnc_app2),
                                 wave(cnc_app2),wave(cnc_cons1)]).
needs(thm(singlerev),   	[def(rev)]).
needs(def(nth),         	[synth(nth)]).
needs(thm(nthnil),      	[def(nth)]).
needs(thm(nthmem),      	[def(nth),def(member)]).
%  NOTE: depth-first this plan is very fragile - the induction method
%  gets the right induction only by luck.  It would be interesting to 
%  see if you could analyse a solid principle to ensure the right 
%  induction is chosen.
needs(thm(nthapp),       	[def(nth),def(plus)]).
needs(thm(nthnth1),             [def(nth),def(pred),def(hd),def(tl)]).
needs(thm(nthnth2),             [def(nth),def(pred),def(hd),def(tl)]).
needs(def(flatten),     	[synth(flatten)]).
needs(synth(flatten),   	[def(nestedlist),def(app)]).
needs(def(flattenmc),   	[synth(flattenmc)]).
needs(synth(flattenmc), 	[def(nestedlist)]). 		% NOT IMPLEMENTED (YET)
needs(def(tree),        	[def(node),def(leaf)]).
needs(def(maxht),       	[synth(maxht), def(max)]).
needs(synth(maxht),     	[def(tree)]). 			% NOT IMPLEMENTED (YET)
needs(def(minht),       	[synth(minht), def(min)]).
needs(synth(minht),     	[def(tree)]). 			% NOT IMPLEMENTED (YET)
needs(scheme(treeind),  	[def(tree)]). 			% NOT IMPLEMENTED (YET)
needs(thm(minmaxgeq),   	[def(min),def(max),def(geq),scheme(pairs)]).
% COULD DO IF WE DEFINE maxht minht using shell
needs(thm(maxhtminht),  	[def(maxht),def(minht),def(geq),wave(minmaxgeq)]).
needs(def(ordered),     	[synth(ordered),def(greater)]). % [def(hd),lemma(decordered)]).
needs(lemma(decordered),	[def(hd),lemma(declessint),lemma(deceqint)]).
needs(def(pairlist),    	[synth(pairlist)]).
needs(thm(mapcarapp),   	[def(mapcar),def(app)]).
needs(thm(lenmapcar),   	[def(mapcar),def(length),wave(cnc_s)]).
needs(thm(revmapcar),   	[def(mapcar),def(rev),wave(cnc_cons1)]).
needs(def(subset),      	[def(member),def(true)]).
% FAILS: To succesfully prove this example we need to apply
% case-analyses in symbolic evaluation
needs(thm(subsetcons),  	[def(subset)]).
needs(def(intersect),   	[synth(intersect),lemma(decmember)]).
needs(synth(intersect), 	[def(member),lemma(decmember)]).
needs(def(union),       	[def(member),synth(union),lemma(decmember)]).
needs(synth(union),     	[def(member),lemma(decmember)]).
needs(def(insert),      	[lemma(decless2)]).
needs(def(sort),        	[def(insert)]).
needs(thm(ord),                 [def(sort),def(ord)]).
needs(thm(ordsort),             [def(ordered),def(sort)]). 
needs(thm(lensort),     	[def(length),def(sort)]).
needs(thm(subsetunion), 	[def(subset),def(union)]).
needs(thm(subsetintersect),	[def(subset),def(intersect),wave(cnc_cons1)]).
needs(thm(memunion1),   	[def(member),def(union)]).
needs(thm(memunion2),   	[def(member),def(union)]).
needs(thm(memintersect),	[def(member),def(intersect)]).
needs(def(assoc),       	[synth(assoc),lemma(deceqintlist)]).
needs(thm(leqnth),      	[def(leq),def(length),def(nth)]).
needs(thm(memins),		[def(member),def(insert)]).
needs(thm(meminsert1),  	[def(member),def(insert)]).
needs(thm(meminsert2),  	[def(member),def(insert)]).
needs(thm(memsort1),    	[def(member),def(sort)]).
% NOTE: Thisneeds a lemma because it otherwise misses a necessary
% generalisation - sigh.
needs(thm(memsort2),    	[def(member),def(sort),wave([meminsert1,meminsert2])]).  
needs(def(count),       	[]).
needs(thm(countsort),   	[def(sort),def(count),wave(cnc_s)]).
needs(thm(cnc_app),		[def(app)]).
needs(def(rotate),       	[def(app)]).
needs(thm(rotlen),       	[def(rotate),def(length),
                                 wave(assapp),wave(assconsapp)]). 
needs(thm(rotlenapp),       	[def(rotate),def(length)]).
needs(thm(rotapp),              [def(rotate),def(length)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% factors synthesis proof (as presented in ``Turning Eureka Steps into
% Calculations in automatic program synthesis'', Bundy, Hesketh and Smaill,
% In proceedings of UK IT `90 (Andrew Ireland, July 91).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(posint),		[def(greater)]).
needs(thm(cnc_posint_times),	[def(times)]).
needs(thm(prod_times),	        [def(prod),def(times)]).
needs(thm(factors),	        [def(posint),
				 def(prod),def(prime),
				 wave(cnc_posint_times),
				 wave(prod_times),
				 scheme(primescheme)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tcons (tail-cons) synthesis proof (as presented in blue book note 636).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(tcons),	 	[def(app),wave(cnc_cons)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% induction scheme stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(lemma(dec_div),   	[def(divides)]).
needs(lemma(fstprime),  	[lemma(dec_div)]).
needs(scheme(primescheme),    	[def(times),def(prime),lemma(fstprime),
				 def(acc_ord)]).
needs(scheme(primec),   	[def(times),def(prime),lemma(primelem)]).
needs(scheme(twos),     	[def(plus)]).
needs(scheme(plusind),  	[def(plus)]).
needs(scheme(pairs),            [def(fst),def(snd),def(pairord)]).
needs(scheme(list_pairs),       [def(fst),def(snd),def(lpairord),
                                 lemma(declist)]). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fibonacci and gcd synthesis:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
 * Taken out for the moment since Jane/AlanS use other defs.
 * 
 *needs(def(fib),              [synth(fib)]).
 *needs(synth(fib),            [def(plus),def(pred)]).
 *needs(def(gcd),              [synth(gcd)]).
 *needs(synth(gcd),            [def(minus)]).
 *
 */
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic-geometric means:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(prod),        	[def(times)]).
needs(def(sum),         	[def(plus)]).
needs(scheme(exp2),     	[def(p),def(times)]).
 /* Cannot prove this yet. Real work remains to be done before this will
  * be possible. Currently deleted for benchmarking purposes.
  *needs(thm(means),    [def(sum),def(prod),def(exp),def(times),def(geq),
  *                       red(plus1right),red(plus2right),red(times1right),
  *                       red(times2right),
  *                       wave(exptimestwo),wave(exptimes),wave(evensum),
  *                       wave(timesexp),wave(timesexptwo),wave(assm),
  *                       % scheme(times2),      % <- still to do
  *                       wave(expprod)          % <- still to do
  *                      ]).
  */
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% method dependencies:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(mthd(ind_strat/1),        [smthd(induction/2),
				 smthd(base_case/1),
				 smthd(step_case/1)]).

needs(smthd(base_case/1),	[smthd(elementary/1),
			 	 smthd(sym_eval/1)]).

needs(smthd(step_case/1),	[smthd(ripple/1),
				 smthd(fertilize/2)]).

needs(mthd(base_case/1),	[smthd(elementary/1),
			 	 smthd(sym_eval/1)]).

needs(mthd(step_case/1),	[smthd(ripple/1),
				 smthd(fertilize/2),
				 smthd(base_case/1)]).

needs(smthd(sym_eval/1),        [smthd(equal/2),
				 smthd(reduction/2),
				 smthd(eval_def/2),
				 smthd(existential/2)]).

needs(smthd(ripple/1),          [smthd(wave/3),
				 smthd(casesplit/1),
				 smthd(unblock/3)]).

needs(smthd(fertilize/2),	[smthd(fertilization_strong/1),
				 smthd(fertilization_weak/1)]).

needs(mthd(weak_fertilize/2),   [smthd(weak_fertilize_right/1),
                                 smthd(weak_fertilize_left/1)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(mthd(normalize/1), 	[smthd(normal/1)]).
needs(smthd(normalize/1), 	[smthd(normal/1)]).
needs(smthd(normal/1),          [smthd(apply_lemma/1),
   			         smthd(backchain_lemma/1)]).

needs(mthd(ripple/1),           [smthd(wave/3),
				 smthd(casesplit/1),
				 smthd(unblock/3)]).

needs(mthd(sym_eval/1),         [smthd(equal/2),
				 smthd(reduction/2),
				 smthd(eval_def/2),
				 smthd(existential/2)]).

needs(mthd(fertilize/2),	[smthd(fertilization_strong/1),
				 smthd(fertilization_weak/1)]).

needs(smthd(fertilization_weak/1),       
				[smthd(fertilize_then_ripple/1),
				 smthd(sym_eval/1),
				 smthd(elementary/1)]).

needs(smthd(fertilize_then_ripple/1),          
				[smthd(fertilize_left_or_right/2),
				 smthd(ripple_and_cancel/1)]).

needs(smthd(fertilize_left_or_right/2),   	
				[smthd(weak_fertilize_left/1),
                                 smthd(weak_fertilize_right/1)]).

needs(smthd(weak_fertilize_left/1),
		                [smthd(weak_fertilize/4)]).

needs(smthd(weak_fertilize_right/1),
		                [smthd(weak_fertilize/4)]).

needs(smthd(ripple_and_cancel/1),
		             	[smthd(cancellation/2),
				 smthd(wave/3),
				 smthd(unblock/3)]).

needs(mthd(ind_strat_I/1),      [mthd(induction_I/2),
				 mthd(base_case/1),
				 mthd(step_case/1)]).


% bottom clause to ensure success with no things needed (default case).
needs(_,[]).

\
/*
 * This file should contain all the needs/2 clauses to record
 * dependencies between logical objects such as definitions, theorems,
 * lemma's etc. 
 */

/*
 * We could of course also record the dependencies between thm's and
 * mthd's (i.e. which methods do we need to prove a particular thm), but
 * somehow this seemed not appropriate.
 */

% Declare dynamic so that users can modify this database with their own
% clauses, using assert/retract.
:- dynamic needs/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Quantified Boolean Logic
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(true), [def(bool)]).
needs(def(false), [def(bool)]).
needs(def(not),  [def(true),def(false)]).
needs(def(and),  [def(true),def(false)]).
needs(def(or),   [def(true),def(false)]).
needs(def(xor),  [def(not),def(and),def(or)]).
needs(def(imp), [def(or),def(not)]).
needs(def(iff), [def(imp),def(and)]).
needs(def(all), [def(and),def(true),def(false)]).
needs(def(some), [def(or),def(true),def(false)]).
needs(def(tr),    [def(true),def(false),def(bool)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Miscellaneous
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(pnatEq), [synth(pnatEq)]).
needs(def(hd),     [synth(hd)]).
needs(def(word),   [def(bool)]).
needs(def(vec),    [def(pnat_eq),def(true),def(false)]).
needs(def(bitval),     [def(bool_eq),def(true),def(false)]).
needs(def(val),    [def(plus),def(times),def(exp),def(bitval),def(vec)]).
needs(def(boolVal),  [def(pnat_eq),def(minus),def(true),def(false),def(exp),
                      def(arb)]).
needs(def(boolV),    [def(not),def(false)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% full adder (Functional Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(addoneTest),  [thm(faSum),thm(faCarry),def(addone)]).
needs(def(addone),  [thm(addonet)]).
needs(thm(faSum),  [mthd(bool_cases/1),def(false),def(true),def(bool),
                    def(not),def(or),def(and),def(xor),def(faSum),
                    def(faSumImp)]).
needs(thm(faCarry),  [mthd(bool_cases/1),def(false),def(true),def(bool),
                     def(not),def(or),def(and),def(xor),def(faCarry),
                     def(faCarryImp)]).
needs(def(faSum),    [def(not),def(and),def(or)]).
needs(def(faSumImp),  [def(xor)]).
needs(def(faCarry),    [def(or),def(and)]).
needs(def(faCarryImp),  [def(or),def(and)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Adder (big endian, parameterized Functional Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(nAdderVer),  [def(nAdderSpec),def(nAdderImp),wave(cnc_s),
                        wave(cnc_cons_bool),wave(cnc_cons_eq),
                        wave(cnc_wordVal),mthd(normal/1),mthd(bool_cases/1),
                        smthd(weak_fertilize/4),mthd(term_cancel/1),
                        wave(plus2right),wave(boolV3)]).
needs(thm(nAdderWord), [thm(nAdderVer),def(wordVal)]).
needs(def(nAdderSpec),  [def(true),def(numVal),def(wordVal),
                         def(bitval),def(plus)]).
needs(def(nAdderImp),  [def(faSum),def(faCarry),def(hd),def(tl)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Adder (BIG endian, unparameterized Functional Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(nAdderNBVer), [def(bool),def(true),def(false),def(word),
                        def(nAddB),def(nAdderB),def(incB),
                        red(plusOne),red(plusZero),
                        wave(incNBsuc),wave(lenIncB),
                        wave(nAdderBinc),
                        def(w2nNB),def(bitval)]).

needs(def(nAdderB), [def(less),def(minus), def(length),def(leadzeroes)]).
needs(def(nAddB), [def(faSum),def(faCarry),def(tl),def(hd)]).
needs(def(incB), [def(nAddB),def(zeroes),def(length),def(true)]).
needs(def(w2nNB), [def(plus),def(bitval),def(times)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Adder (little endian, parameterized Functional Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(adderPLVer), [def(bool),def(true),def(false),def(word),
                        def(adderSpecPL),def(w2nPL),def(adderPL)]).
needs(def(adderSpecPL), [def(plus),def(w2nPL),def(bitval)]).
needs(def(adderPL), [def(addPL),def(hd),def(tl)]).
needs(def(addPL), [def(faCarry),def(faSum),def(hd)]).
needs(def(w2nPL), [def(plus),def(times),def(bitval),def(exp),def(length),
                   def(hd),def(tl)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Adder (little endian, unparameterized Functional Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(caddVer),   [def(bool),def(true),def(false),def(word),
                       def(cadd),def(word2nat),def(bitval),
                       red(plusOne),red(plusZero),red(timesOne),
                       wave(cnc_exptwo),
                       wave(commplus3),wave(commplus4),
                       wave(len_cadd),wave(len_cadd2),
                       wave(len_cadd3),wave(len_cadd4),
                       lemma(cadd_no_nil),
                       mthd(backchain_lemma/_),mthd(replace_head/_)]).


needs(thm(cadderVer), [def(bool),def(true),def(false),def(word),
                       def(cadd),def(cadder),def(inc),
                       red(plusOne),red(plusZero),
                       wave(incsuc),wave(lenInc),wave(cadderInc),
                       def(word2nat),def(bitval)]).
                       
needs(def(cadder), [def(less),def(minus),def(length),def(leadzeroes)]).
needs(def(inc), [def(cadd),def(zeroes),def(length),def(true)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Converts
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(numVal),     [def(plus),def(times),def(bitval),def(hd),def(tl)]).
needs(def(wordVal),    [def(boolV),def(half),def(word)]).
needs(def(natFromInt), [def(p)]).
needs(def(intFromWord),  [def(nBitW),def(intFromNat),def(numVal),def(twoCompW),
                          def(true)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Artithmetic, Logic and Shift Operations on Words (Functional Representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(andW),      [def(word),def(and),def(hd),def(tl)]).
needs(def(orW),       [def(word),def(or),def(hd),def(tl)]).
needs(def(xorW),      [def(word),def(xor),def(hd),def(tl)]).
needs(def(notW),      [def(word),def(not),def(hd),def(tl)]).
needs(def(incW),      [def(word),def(bool),def(wordVal),def(addW)]).
needs(def(decW),      [def(word),def(bool),def(wordVal),def(subtractW)]).
needs(def(twoComW),      [def(word),def(incW),def(notW)]).
needs(def(addW),      [def(bool),def(word),thm(faSum),thm(faCarry),def(hd),def(tl)]).
needs(def(subtractW),      [def(addW),def(notW)]).
needs(def(move),     [def(not),def(and),def(app)]).
needs(def(nBitW),     [def(false),def(pnatEq),def(hd),def(tl)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit ALU (Parameterized, BIG endian, functional Representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(oneAluSpec), [def(nAluSpec)]).
needs(def(oneAluImp),  [def(bool),thm(faSum),def(or),def(and),def(not),
                        thm(faCarry)]).
needs(def(aluHead),  [def(hd),def(oneAluImp)]).
needs(def(aluCarry),  [def(hd),def(oneAluImp)]).
needs(thm(oneAluVer), [def(bool),def(word),def(bool_eq),def(false),def(true),
                       def(addW),def(subtractW),def(incW),def(decW),def(orW),
                       def(xorW),def(andW),def(notW),def(app),def(move),
                       def(trunc),def(nBitW)]).

needs(def(nAluSpec), [def(bool),def(word)]).
needs(def(nAluImp), [def(aluHead),def(aluCarry)]).
needs(thm(nAluVer), [def(bool),def(word),def(bool_eq),def(false),def(true),
                     def(hd),def(tl),
                     def(addW),def(subtractW),def(incW),def(decW),def(orW),
                     def(xorW),def(andW),def(notW),def(app),def(move),
                     def(trunc),def(nBitW),def(twoCompW),def(natFromInt),
                     def(moveWordNC),def(moveWordWC),def(incW),def(decW),
                     thm(nAdderVer)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ALU Properties
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(nAluProp10), [def(nSubtractIntSpec),def(addInt),
                       def(changeSign),def(intFromNat),def(bitval),
                        def(intFromWord),def(true),def(false),
                        def(subtractInt),lemma(negZero),def(nAluImpGood)]).

needs(def(subtractInt), [def(addInt),def(changeSign)]).
needs(def(nSubtractIntSpec), [def(subtractInt),def(intFromWord),
                              def(intFromNat),def(bitval)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit ALU (Nonparameterized, little endian, functional representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(aluVerNL), [def(bool),def(true),def(false),def(word),
                     def(bool_eq),def(cadd),def(inc),def(dec),
                     wave(cnc_cons_eq),
                     def(subtractNL),def(movencNL),def(movewcNL),
                     def(andNL),def(orNL),def(xorNL),def(notNL),def(app),
                     def(faSum),def(faCarry),
                     def(and),def(or),def(xor),def(not)]).
                     

needs(def(movencNL), [def(zeroes),def(length)]).
needs(def(subtractNL), [def(cadd),def(notNL)]).
needs(def(andNL), [def(and),def(hd),def(tl)]).
needs(def(orNL), [def(or),def(hd),def(tl)]).
needs(def(xorNL), [def(xor),def(hd),def(tl)]).
needs(def(notNL), [def(not),def(hd),def(tl)]).
needs(def(aluImp), [def(aluAux)]).
needs(def(aluAux), [def(alu1Out),def(alu1Carry)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ALU Properties (Nonparameterized, little endian, functional representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(aluNatVer), [thm(aluVerNL),def(word2nat),
                       def(plus),def(minus),
                       red(plusOne),red(plusZero),red(timesOne),
                       wave(cnc_exptwo),wave(plus2right),
                       wave(commplus3),wave(commplus5),
                       wave(len_alu),wave(len_alu2),
                       wave(len_alu3),wave(len_alu4),
                       wave(comminus),
                       lemma(alu_no_nil),
                       mthd(backchain_lemma/_),mthd(replace_head/_)]).

needs(def(aluSpecNat), [def(bool),def(bool_eq)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Shift Unit (Functional Representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(muxSpec),  [def(hd),def(tl)]).
needs(def(muxImp),   [def(or),def(and),def(not),def(hd),def(tl),def(wordVal)]).
needs(thm(muxVer),   [def(muxSpec),def(muxImp)]).
needs(def(une),      [def(app)]).
needs(def(shiftSpec), [def(bool),def(word),def(app),def(wordVal),
                       def(rev),def(hd),def(tl),def(bool_eq),
                       def(false),def(true)]).
needs(def(shiftImp),  [def(muxImp),def(hd),def(tl),def(bool),def(true),
                       def(false),def(word)]).
needs(def(shiftImpGood),  [def(shiftImp)]).
needs(thm(shiftVer),    [def(shiftSpec),def(shiftImpGood),
                         wave(cnc_cons_bool),
                         def(length),mthd(replace_head2/_)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% nm-bit Multiplier
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(multVer2), [def(word2nat),def(app),wave(assm),wave(assAppCons),
                     wave(appMultZero),wave(timesTwo)]).
/*
needs(thm(multVer), [def(word2nat),def(mult),wave(caddVerMult),
                     wave(distTimesPlus),
%                    wave(distTimesPlus2),
                     wave(assm),wave(assTimes1),
                     wave(assTimes2),
                     wave(appMultZero),wave(assAppCons),wave(timesTwo),
                     wave(cnc_s),
                     red(appNil),red(timesZero),red(plusZero),red(timesOne),
                     red(timesZero)]).
*/

needs(def(mulSpec), [def(times),def(word2nat)]).
needs(def(word2nat), [def(plus),def(times),def(bitval),def(exptwo),
                      def(length)]).
needs(def(mult), [def(appnd),def(multOne),def(zeroes),def(length),def(cadd)]).
needs(def(cadd), [def(add),def(hd),def(tl)]).
needs(def(add), [def(faCarry),def(faSum),def(hd),def(tl)]).
needs(def(multOne), [def(and)]).
needs(def(zeroes), [def(false)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% increment
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(incVer), [def(bool),def(true),def(false),def(word),
                       def(incword),def(word2nat),def(bitval),
                       red(plusOne),red(plusZero),red(timesOne),
                       wave(cnc_exptwo),wave(plus2right),
                       lemma(inc_no_nil),
                       mthd(backchain_lemma/_),mthd(replace_head/_)]).

needs(def(incword), [def(incaux)]).
needs(def(incaux),  [def(incbit),def(cincbit),def(hd),def(tl)]).
needs(def(incbit),  [def(xor)]).
needs(def(cincbit),  [def(and)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% equivalence of times
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(timesVer), [def(times),def(timesW),wave(plusVer)]).
needs(def(timesW), [def(word2nat),def(plusW)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Factorial
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(factVer), [def(word2nat),def(fac),def(facW),wave(multVer),
                     wave(incsuc),red(plusZero),wave(cancelProd),
                     thm(cancelProd3)]).

needs(def(facW), [def(true),def(word),def(inc),def(mult),def(nat2word)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Exponentiation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(expVer), [def(exp),def(expW),wave(multVer),wave(incsuc)]).
needs(def(expW), [def(word2nat),def(true),def(mult)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Plus
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(plusVer), [def(plus),def(plusW),wave(incsuc),wave(cnc_s)]).
needs(def(plusW), [def(word2nat),def(inc)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Minus
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(minusVer), [def(minus),def(minusW),wave(decPred),wave(incsuc)]).
needs(def(minusW), [def(word2nat),def(dec),def(tl)]).
needs(def(dec), [def(ones)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Divider
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(divVer), [def(div),def(divW),
                    wave(plusVer),wave(divWplusW),wave(divPlus)]).
needs(def(divW), [def(word2nat),def(mult),def(inc)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Remainder
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(remVer), [def(word2nat),def(rem),def(remW),
                    wave(minusinc),wave(incsuc),wave(minusuc),wave(cnc_s),
                    wave(divinc),wave(divsuc),wave(distTimesPlus2),
                    red(plusZero),red(plusWzero)]).
needs(def(rem), [def(inc),def(minus),def(plus),def(times),def(div)]).
needs(def(remW), [def(word2nat),def(inc),def(minusW),def(plusW),
                  def(timesW),def(divW)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Records and Flip Flops
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(def(jkFF),  [def(bool),def(true),def(false),def(or),def(and),def(not)]).
needs(def(oneReg), [def(jkFF),def(and),def(not)]).
needs(def(register), [def(oneReg),def(hd),def(tl)]).

needs(def(reg),    [def(word)]).
needs(def(flip),  [def(bool)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Counter (sequential)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% bizarre version
needs(thm(counterVer), [def(counter),def(counterImp),def(word2nat),
                        wave(incsuc),wave(w2nDel),wave(incDel),
                        wave(delayInc),red(delayTrue),mthd(apply_lemma/_)]).
needs(def(counter), [def(bool_eq),def(rem),def(exp),def(true),
                     def(nat2word),def(length),def(false),def(word)]).
% def(reset),def(pred)
needs(def(inp),   [def(reg)]).
needs(def(reset),  [def(flip)]).

needs(def(delay), [def(word)]).
% [def(inp)]).
needs(def(initial), [def(bool_eq),def(true),def(zeroes),
                     def(length)]).
% def(reset),def(initVal)
needs(def(initVal), [def(reg)]).
needs(def(increm), [def(value),def(tl),def(inc)]).
needs(def(counterImp), [def(delay),def(initial),def(inc)]).
% def(increm)


%better version

needs(thm(countVer), [def(countSpec),def(countImp),def(word2nat),
                      def(flip),def(reg),def(length),
                      wave(incsuc),mthd(apply_lemma/_)]).
needs(def(countImp), [def(zeroes),def(restart),def(incfun),def(del),
		      def(nat2word)]).
needs(def(countSpec), [def(bool_eq),def(rem),def(exp)]).
needs(def(del),      [def(pred)]).
needs(def(restart), [def(bool_eq),def(zeroes)]).
needs(def(incfun),  [def(inc)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 1-bit Adder verification (Relational Representation)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(faVer), [def(faSpec),def(faImp),mthd(bool_cases/1),mthd(lambdaRed/1),def(tr)]).
needs(def(faSpec), [def(plus),def(times),def(bitval),def(bool)]).
needs(def(faImp), [def(some),def(and),def(xorG),def(orG),def(andG),def(bool)]).
needs(def(andG), [def(iff),def(and),def(not),def(true),def(false),def(bool)]).
needs(def(orG),[def(iff),def(or),def(not),def(true),def(false),def(bool)]).
needs(def(notG),[def(iff),def(not),def(true),def(false),def(bool)]).
needs(def(xorG),[def(iff),def(xor),def(not),def(true),def(false),def(bool)]).
needs(def(nandG),[def(iff),def(and),def(not),def(true),def(false),def(bool)]).
needs(def(norG),[def(iff),def(or),def(not),def(true),def(false),def(bool)]).


needs(def(nAdder),   [thm(nAdder),def(val),def(boolVal)]).
needs(thm(nAdder),   [def(word),def(bool)]).
needs(thm(nAdderTest),  [def(nAdder),def(vecA),def(vecB),def(vecS)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% n-bit Adder (Relational Representation):
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

needs(thm(adder),  [def(bool),def(tt),def(ff),def(or),def(vector),def(tr),def(exp),def(val),def(iff),def(exb),def(and),def(xor),def(adder)]).
needs(def(adder),    [def(iff),def(exb),def(and),def(add1),thm(adderdefp)]).
needs(thm(assoc1), [def(assoc)]).
needs(thm(t1), [wave(cnc_s),thm(assm)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(times),       [def(plus)]).
needs(def(divides),     [def(times)]).
needs(def(minus),       [def(pred)]).
needs(def(prime),       [def(posint),def(divides)]).
needs(def(prodl),       [def(times)]).
needs(def(even),        [synth(even),def(true)]).
needs(def(odd),         [synth(odd),def(true)]).
needs(def(half),        [synth(half)]).
needs(def(facv),         [def(times)]).
needs(thm(cnc_times),    [def(times),mthd(normalize/_)]).
needs(thm(cnc_pnat_times), [def(times),mthd(normalize/_)]).
needs(thm(cnc_s),       [mthd(normalize/_)]).
needs(thm(assp),        [def(plus),wave(cnc_s)]).
needs(thm(assp2),       [def(plus),wave(cnc_s)]).
needs(thm(assm),        [def(times)]).
needs(thm(comm),        [def(times)]).
% <*
needs(thm(commtwo),     [def(times),scheme(plusind),wave(disttwo),wave(dist)]).
needs(thm(plus1right),  [def(plus)]).
needs(thm(plus2right),  [def(plus)]).
needs(thm(times1right), [def(times)]).
% <*
needs(thm(times2right), [def(times)]).
needs(thm(commthree),   [def(times),wave(disttwo),wave(times2right)]).
% <*
needs(thm(binom_one),   [def(minus),def(plus),def(binom),red(plus1right),red(plus2right)] ).
% <?  Fails would you believe!
needs(thm(comp),        [def(plus)]).
needs(thm(comp2),       [def(plus)]).
% <*
needs(thm(dist),        [def(plus),def(times)]).
% <*
needs(thm(disttwo),     [def(plus),def(times)]).
needs(synth(even),      [scheme(twos)]).
needs(synth(odd),       [scheme(twos)]).
needs(synth(half),      [scheme(twos)]).
needs(synth(plus),      []). %[scheme(prim)]).
needs(def(leq),         [def(true)]).
needs(def(geq),         [def(true)]).
% <*
needs(thm(minmax),      [def(min),def(max),def(leq)]).
% <*
needs(thm(lesss),       [def(less)]).
needs(thm(zeroplus),    [def(plus)]).

% <* 
needs(thm(zerotimes),   [def(times),wave(zeroplus)]).
needs(thm(zerotimes1),  [def(times)]).
% <*
needs(thm(zerotimes2),  [def(times)]).
needs(thm(geqnotlessp), [def(geq),def(less)]).
% <*
needs(thm(lesstrich),   [def(less),def(greater),wave(funcs)]).
% <*
needs(thm(plusgeq),     [def(plus),def(geq)]).
% <*  
needs(thm(plusgeq2),    [def(plus),def(geq),wave(plus2right)]).
needs(thm(evendouble),  [def(even),def(double)]).
needs(thm(halfdouble),  [def(half),def(double)]).
needs(thm(doublehalf),  [def(half),def(even),def(double),wave(funcs)]).
% <* CHECK that 1st sub-goals FAILS ON ARCHY TOO!
needs(thm(doubletimes1), [def(double),def(times),wave(times2right)]).
% <*
needs(thm(doubletimes2),[def(double),def(times)]).
needs(def(exp),         [def(times)]).
% <*
needs(thm(expplus),     [def(exp),def(plus),wave(disttwo),wave(dist),
                         scheme(plusind), red(times1right),red(times2right),
                         red(plus1right)]).
% <*
needs(thm(exptimes),    [def(exp),def(times),scheme(plusind),wave(expplus),
                         wave(dist)]).
% <*
needs(thm(evenodd1),    [def(even),def(odd)]).
% <*
needs(thm(evenodd2),    [def(even),def(odd)]).
% <*
needs(thm(lesstrans1),   [def(less)]).
% <*
needs(thm(lesstrans2),  [def(less),def(leq)]).

needs(thm(lesstrans3),  [def(less)]).
needs(thm(notlesstrans),[def(less),def(leq)]).
needs(thm(notlesstrans2),[def(less),def(leq)]).
needs(thm(notlesstrans3),[def(leq)]).
needs(thm(notleqreflex),[def(leq)]).
needs(thm(lesseq),      [def(less),def(leq),wave(funcs)]).
needs(thm(leqtrans),    [def(leq)]).
% <*
needs(thm(greatertrans),[def(greater)]).
needs(thm(greatercons), [def(greater),def(length)]).
needs(thm(leqdupl),     [def(leq)]).
needs(thm(leqdouble),   [def(leq),def(double)]).
needs(thm(leqhalf),   [def(leq),def(half)]).
needs(thm(leqhalfdouble),   [def(leq),def(half),def(double)]).
needs(thm(cnc_half),    [def(half),mthd(normalize/_)]).
needs(thm(halfpnat),	[def(plus),def(half),wave(cnc_s),wave(cnc_half)]).
needs(thm(greaterplus), [def(greater),def(plus)]).
needs(thm(greaterplus2), [def(greater),def(plus)]).
needs(thm(greaterplus3), [def(greater),def(plus)]).
needs(thm(greatertimes),[def(greater),def(times),
                         mthd(apply_lemma/_),thm(greaterplus)]).
needs(thm(greaters),    [def(greater)]).
needs(thm(greaters2),    [def(greater)]).
needs(thm(greatercancel),[def(greater),def(times)]).
needs(thm(grsqsuc),[def(greater),def(times)]).
needs(thm(geqhalf),[def(geq),def(half)]).
needs(thm(geqdouble),[def(geq),def(double)]).
needs(thm(geqdoublehalf),[def(geq),def(double),def(double)]).
needs(thm(cnc_pred),    [def(pred),mthd(normalize/_)]).
needs(thm(minus_pred),   [def(minus),wave(cnc_pred)]).
needs(thm(minus_succ),   [def(minus),wave(cnc_pred)]).
needs(thm(minus_plus), [def(plus),def(minus),wave(cnc_pred)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% primefac stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(evenp),       [def(even),scheme(twos)]).
needs(thm(prodl),       [def(prodl),def(pnatapp),def(times),
                         mthd(apply_lemma/_),thm(assm)]).
% <*
 
needs(thm(prodlwave),   [def(prodl),def(pnatapp),def(times),
                         mthd(apply_lemma/_), thm(assm)] ).
needs(lemma(identrm),   [def(times)]).
needs(lemma(not0lm),    [def(times)]).
needs(lemma(not0rm),    [def(times)]).
% NOTE: Can not prove primefac (version 1.4 or 1.5). I (AndrewS)
% am working on this - it requires a lot of middle-out stuff to be
% properly sorted: checking types of solution terms are sensible
% controlling symbolic evaluation, conditional fertilization ....
% Probably proper control of potential wave-fronts etc as well

% <-
% needs(thm(primefac),   [def(prime),def(prodl),scheme(primec),wave(prodlwave),
%                         red(identrm),lemma(not0lm),lemma(not0rm)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% list stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(rev),         [def(app)]).
needs(thm(litapp),      [def(app),def(lit)]).
needs(thm(apprev),      [def(app),def(rev)]).
needs(thm(assapp),      [def(app)]).
needs(thm(comapp),      [def(app),def(length)]).

needs(thm(lenrev),      [def(length),def(rev)]).
needs(thm(lenapp),      [def(length),def(app)]).
% <*
needs(thm(lensum),      [def(length),def(app),def(plus)]).
needs(def(member),      [def(true),lemma(deceqint)]).
needs(thm(memapp1),      [def(member),def(app)]).
% <*
needs(thm(memapp2),     [def(member),def(app)]).
% <*
needs(thm(memapp3),     [def(member),def(app)]).
needs(thm(app1right),   [def(app)]).
% FAILED: No support for rippling disjunctive waves: I.e.
%     WAVE: {A}\B :=> A, COMP-REWRITE {A}\B :=> B
% OR  WAVE: A\{B} :=> B, COMP-REWRITE A\{B} :=> A
needs(thm(memrev),      [def(member),def(rev),wave(memapp3)]).
% <*
needs(thm(revrev),      [def(rev)]).
needs(thm(revqrev),     [def(rev),def(qrev),wave(assapp)]).
needs(thm(tailrev),     [def(rev),def(app)]).
needs(thm(tailrev2),    [def(rev),def(app)]).

% <*
needs(thm(singlerev),   [def(rev)]).
needs(def(nth),         [synth(nth)]).
needs(thm(nthnil),      [def(nth)]).
needs(thm(nthmem),      [def(nth),def(member)]).
% <*  NOTE: depth-first this plan is very fragile - the induction method
%  gets the right induction only by luck.  It would be
% interesting to see if you could analyse a solid principle
% to ensure the right induction is chosen.
needs(thm(nthapp),      [def(nth),def(plus)]).
needs(def(flatten),     [synth(flatten)]).
needs(synth(flatten),   [def(nestedlist),def(app)]).
needs(def(flattenmc),   [synth(flattenmc)]).
needs(synth(flattenmc), [def(nestedlist)]). % NOT IMPLEMENTED (YET)
needs(def(tree),        [def(node),def(leaf)]).
needs(def(maxht),       [synth(maxht), def(max)]).
needs(synth(maxht),     [def(tree)]). % NOT IMPLEMENTED (YET)
needs(def(minht),       [synth(minht), def(min)]).
needs(synth(minht),     [def(tree)]). % NOT IMPLEMENTED (YET)
needs(scheme(treeind),  [def(tree)]). % NOT IMPLEMENTED (YET)
% <* 
needs(thm(minmaxgeq),   [def(min),def(max),def(geq)]).
% COULD GO IF WE DEFINE maxht minht using shell
%needs(thm(maxhtminht),  [def(maxht),def(minht),def(geq),wave(minmaxgeq)]).
needs(def(ordered),     [def(hd),lemma(decordered)]).
%needs(lemma(decordered),[def(hd),lemma(declessint),lemma(deceqint)]).
needs(def(pairlist),    [synth(pairlist)]).
% <*
needs(thm(mapcarapp),   [def(mapcar),def(app)]).
% <*
needs(thm(lenmapcar),   [def(mapcar),def(length)]).
% <*
needs(thm(revmapcar),   [def(mapcar),def(rev),wave(funccons1)]).
needs(def(subset),      [def(member),def(true)]).
% FAILS: To succesfully prove this example we need to apply
% case-analyses in symbolic evaluation
needs(thm(subsetcons),  [def(subset)]).
needs(def(intersect),   [synth(intersect),lemma(decmember)]).
needs(synth(intersect), [def(member),lemma(decmember)]).
needs(def(union),       [def(member),synth(union),lemma(decmember)]).
needs(synth(union),     [def(member),lemma(decmember)]).
needs(def(insert),      [lemma(decless)]).
needs(def(sort),        [def(insert)]).
% <*
needs(thm(lensort),     [def(length),def(sort)]).

% <*
needs(thm(subsetunion), [def(subset),def(union)]).
needs(thm(subsetintersect),[def(subset),def(intersect),wave(funccons1)]).
% <*
needs(thm(memunion1),   [def(member),def(union)]).
% <*
needs(thm(memunion2),   [def(member),def(union)]).
% <*
needs(thm(memintersect),[def(member),def(intersect)]).
needs(def(assoc),       [synth(assoc),lemma(deceqintlist)]).

needs(thm(leqnth),      [def(leq),def(length),def(nth)]).

needs(thm(meminsert1),  [def(member),def(insert)]).
needs(thm(meminsert2),  [def(member),def(insert)]).
needs(thm(memsort1),    [def(member),def(sort)]).
% <* NOTE: This needs a lemma because it otherwise misses a necessary
%          generalisation - sigh.
needs(thm(memsort2),    [def(member),def(sort),wave([meminsert1,meminsert2])]).  
% <* lemma(memins)]).
needs(def(count),       [lemma(deceqint)]).
% <*
needs(thm(countsort),   [def(sort),def(count),wave(funcs)]).

needs(thm(cnc_app),	 [def(app),mthd(normalize/_)]).
needs(def(rotate),       [def(app),def(hd),def(tl)]).
needs(thm(rotlen),       [def(rotate),def(app),def(length),red(app1right),
                          wave(assapp),wave(cnc_app)]). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% factors synthesis proof (as presented in ``Turning Eureka Steps into
% Calculations in automatic program synthesis'', Bundy, Hesketh and Smaill,
% In proceedings of UK IT `90.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(posint),		 [def(greater)]).
needs(thm(cnc_posint_times),	 [def(times),def(posint),mthd(normalize/_)]).
needs(thm(prod_times),	         [def(prod),def(times)]).
needs(thm(factors),	         [def(posint),def(prod),def(prime),
				  wave(prod_times),wave(cnc_posint_times),
				  scheme(primescheme)]).
                                  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% tcons (tail-cons) synthesis proof (as presented in blue book note 636.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(thm(cnc_cons),    [mthd(normalize/_)]).
needs(thm(tcons),	 [def(app),wave(cnc_cons)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% induction scheme stuff:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(lemma(dec_div),   [def(divides)]).
needs(lemma(fstprime),  [lemma(dec_div)]).
needs(scheme(primescheme),    [def(times),def(prime),lemma(fstprime),
                               def(acc_ord)]).
needs(scheme(primec),   [def(times),def(prime),lemma(primelem)]).
needs(scheme(twos),     [def(plus)]).
needs(scheme(plusind),  [def(plus)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fibonacci and gcd synthesis:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
 * Taken out for the moment since Jane/AlanS use other defs.
 * 
 * needs(def(fib),              [synth(fib)]).
 * needs(synth(fib),            [def(plus),def(pred)]).
 * needs(def(gcd),              [synth(gcd)]).
 * needs(synth(gcd),            [def(minus)]).
 */

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% arithmetic-geometric means:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
needs(def(prod),        [def(times)]).
needs(def(sum),         [def(plus)]).
needs(thm(cnc_prod),    [def(prod),mthd(normalize/_)]).
needs(scheme(exp2),     [def(p),def(times)]).
/* Cannot prove this yet. Real work remains to be done before this will
/* be possible. Currently deleted for benchmarking purposes.
 * needs(thm(means),    [def(sum),def(prod),def(exp),def(times),def(geq),
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

needs(smthd(normal/1),          [mthd(apply_lemma/1),
                                 mthd(backchain_lemma/1)]).
needs(mthd(ind_strat_I/1),      [mthd(induction/2),
                                 mthd(strong_fertilize/1),
                                 mthd(weak_fertilize/2)]).
needs(mthd(ind_strat_II/1),     [mthd(sym_eval/1),
                                 mthd(weak_fertilize/2)]).

needs(mthd(normalize/1),        [smthd(normal/1)]).
needs(mthd(sym_eval/1),         [smthd(equal/2),
                                 smthd(reduction/2),
                                 smthd(eval_def/2),
                                 smthd(equal_hyp/2),
				 smthd(existential/2)]).
needs(smthd(base_rewrites/1),   [smthd(base/2)]).
needs(mthd(weak_fertilize/2),   [smthd(left_weak_fertilize/1),
                                 smthd(right_weak_fertilize/1)]).
needs(smthd(left_weak_fertilize/1),     [smthd(weak_fertilize/4)]).
needs(smthd(right_weak_fertilize/1),    [smthd(weak_fertilize/4)]).
needs(mthd(minduction/2),       [ mthd(mwave/3) ] ).
needs(mthd(ripple/1),           [ smthd(wave/3),smthd(casesplit/1),smthd(unblock/3)]).
needs(mthd(mwave/3),            [ smthd(wave/3) ] ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% bottom clause to ensure success with no things needed (default case).
needs(_,[]).














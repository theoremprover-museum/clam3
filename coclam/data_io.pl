/************************************************************************

      File: data_io.pl
      Author: Louise Dennis
      Last Modified: 31st July 1997

      semantics for three i/o systems.  See paper "An Operational
      Semantics for I/0 in a Lazy Functional Language", A. Gordon,
      Proc. FPCA'93, pp 136--145, ACM Press.

      NB. Incomplete, requires addition of landin-stream I/0 and the
  inclusion of exceptions.
************************************************************************/

%%%  Ugly extras for type checking of named variables.
data(V, T, [V:T], blip):- \+var(V), atomic(V), var(T), !.
data(V, T, [V:T], blip):- \+var(V), atomic(V), data(_, Ty, _, _), Ty == T, !.

%% continuation passing i/o type
data(input(F), cps, [F:cps], rec).
data(output(V, F), cps, [V:char, F:cps], rec).
data(done, cps, [], non_rec).

data(yes(A), maybe(T), [A:T], non_rec).
data(no, maybe(_), [], non_rec).

data(get, req, [], non_rec).
data(put(V), req, [V:char], non_rec).

data(got(C), ack, [C:char], non_rec).
data(did, ack, [], non_rec).

%% stream transformer type
data(F, st(In, Out), [], non_rec).

%% RWD
data(r, rwd(Out), [], non_rec).
data(w(O), rwd(Out), [O:Out], non_rec).
data(d, rwd(Out), [], non_rec).

%% transition rules for cps 
transition([], input(K), in(N), K of N).
transition([], output(V, Q), out(V), Q).
transition([], done, done, bot).

%% transition rules for stream transformers of ss type.
transition([nextST(F)=no in maybe(req), F:st(ack,req)], F, done, bot).
transition([nextST(F)=yes(get)in maybe(req), F:st(ack, req)], F, in(N),
	skipST(F) of (got(N)::L)).
transition([nextST(F)=yes(put(N))in maybe(req), F:st(ack, req)], F, out(V),
	skipST(F) of (did::L)).

%% transition rules for landin stream
transition([ready(F)=d in rwd(char), F:st(char, char)], F, done, bot).
transition([ready(F)=r in rwd(char), F:st(char, char)], F, in(N),
	F of (N::L)).
transition([ready(F)=w(N) in rwd(char), F:st(char, char)], F, out(N),
	skipST(F)). 

subtype_lang(st(_, _), io).
subtype_lang(cps, io).
data:-consult('~/xclam/data_io.pl').


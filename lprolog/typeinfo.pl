
:- uniq_recorda(hov_cnt, 1, _).
:- uniq_recorda(environment,[],_).
%:- delete_hovs.

:- retractall(type(_,_,_)).
:- assertz(type(clam,'@wave_front@',hs ---> dir ---> T ---> T)).
:- assertz(type(clam,'@wave_var@',T ---> T)).
:- assertz(type(clam,'@sink@', T ---> T)).
:- assertz(type(clam,in,dir)).
:- assertz(type(clam,out,dir)).
:- assertz(type(clam,hard,hs)).
:- assertz(type(clam,soft,hs)).

:- assertz(type(clam,s,    pnat ---> pnat)).
:- assertz(type(clam,plus, pnat ---> pnat ---> pnat)).
:- assertz(type(clam,nth,  pnat ---> (list^pnat) ---> (list^pnat))).
:- assertz(type(clam,even, pnat ---> u(1))).
:- assertz(type(clam,odd,  pnat ---> u(1))).
:- assertz(type(clam,half, pnat ---> pnat)).

:- assertz(type(clam,rev,  (list^pnat)---> (list^pnat))).
:- assertz(type(clam,qrev, (list^pnat)---> (list^pnat)---> (list^pnat))).
:- assertz(type(clam,rev_flatten,  ((list^pnat)^list) ---> (list^pnat))).
:- assertz(type(clam,qrev_flatten, ((list^pnat)^list) ---> (list^pnat) ---> (list^pnat))).
:- assertz(type(clam,app,  (list^pnat)---> (list^pnat)---> (list^pnat))).
:- assertz(type(clam,length,  (list^pnat)---> pnat)).
:- assertz(type(clam,evenl,(list^pnat)---> u(1))).
:- assertz(type(clam,::,   pnat ---> (list^pnat) ---> (list^pnat))).
:- assertz(type(clam,cons, pnat ---> (list^pnat) ---> (list^pnat))).
:- assertz(type(clam,nil,  list^pnat)).






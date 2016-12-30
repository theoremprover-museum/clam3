
/*
 * This file contains predicates that need to be present before we can
 * run the make-scripts.
 * I guess their usual place would otherwise be in util.pl
 */

dialect(swi).
os(unix).

?- ensure_loaded(library(quintus)).
?- op(0,fx,~).
?- op(900,      fy,     [not]).

if(X):-X,!.

% NOTE very weird form of conditional consulting predicates to suit
% quintus' pecadilloes.
% 
if(_) :- current_stream( _,_, S),!,
         ( retractall( if__ctr(_) ) ; true ),
        asserta( if__ctr( 1 ) ),
        'repeat',
         read(S,X),
         count__0(X),
         !.
if(_):- ( retractall( if__ctr(_) ) ; true ),
        asserta( if__ctr( 1 ) ),
        'repeat',
         read(X),
         count__0(X),
         !.

endif.

lib_include(_).

count__0((?-if(_))):-
    retract( if__ctr(PR) ),
    R is PR+1,
    asserta( if__ctr(R)),!,
    fail.
count__0((?-endif)):-
    retract( if__ctr(SR) ),
    R is SR-1,
    ( R = 0 -> true ; asserta( if__ctr(R) ), !,fail ).
count__0(end_of_file):-
    retract( if__ctr( _ ) ),
    asserta( if__ctr( 0 ) ).

/* the three predicates (load/1, reload/1 and time_stamp/1) are
 * part of the make-package. See util.pl for details.
 * IN SWI THIS IS REDUNDANT as it is built into the system...
 */
	% load/1 and reload/1 are as consult/1 and reconsult/1, except
	% that they store a stime stamp for the file.
	% Similarly, loadc/1 is like compile. 
load([]) :- !.
load([F|Fs]) :- !, load(F), load(Fs).
load(File) :- consult(File).
reload([]) :- !.
reload([F|Fs]) :- !, reload(F), reload(Fs).
reload(File) :- consult(File).
loadc([]) :- !.
loadc([F|Fs]) :- !, loadc(F), loadc(Fs).
loadc(File) :- consult(File).

reconsult(F) :- consult(F).

	% time_stamp(+File): produce a time stamp for File. If
	% necessary, throw away existing time stamp.
time_stamp(F) :-
    datime(D), absolute_file_name(F,File),
    (recorded(time_stamp,(File,_),R)->erase(R);true),
    recorda(time_stamp,(File,D),_).

?- if( \+ dialect(huprolog) ).
	% save_state(+String,+File) saves current program state in File. Next
	% time File is called, String will be printed as a banner,
	% followed by the time when the saved state was created.
?- multifile save_state/2.

save_state(String,File) :-
    datime(date(Year,Month1,Day,Hour,Min,_)),
    Month is Month1+1,	% Quintus bug: Month is 1 down.
    name(Atom,String),
    (Hour<10->(Hc is Hour+48,H=[48,Hc]);H=Hour),
    (Min <10->(Mc is  Min+48,M=[48,Mc]);M=Min),
    concat_atom([Atom,' (',Day,'/',Month,'/',Year,' ',H,':',M,')'],Banner),
    version(Banner),
    save(File), version.

?- endif.



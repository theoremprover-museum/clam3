  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                          FILE    DISPLAY.PL                                 %
%                        ----------------------                               %
%                                                                             %
%   Clauses in this file provide a set of displaying routines that are useful %
%   at various places. The main routines defined here are the following:      %
%                                                                             %
%                                                                             %
%   inctab,dectab         :   Functions that set tabs for providing proper    %
%                             indentation.                                    %
%                                                                             %
%   writeblanks(N)        :   Indents a line by an amount proportional to N.  %
%                                                                             %
%   write_tab             :   Indent by an amount determined by the tab       %
%                             setting.                                        %
%                                                                             %
%   newl                  :   Provide a line feed, and indent the new line.   %
%                                                                             %
%   write_line(Line)      :   Display the list of tokens in Line in an        %
%                             appropriate format.                             %
%                                                                             %
%   write_type(Type)      :   Display a lambda Prolog type expression.        %
%                                                                             %
%   write_type_withnames  :   Display a lambda Prolog type, replacing Prolog  %
%    (Type,Cin,Cout,Prec) :   variables used for type variables by readable   %
%			      names					      %
%                                                                             %
%   write_term_lp(Term,Mod)  :   Display a lambda Prolog term in untyped format. %
%                                                                             %
%   write_tyterm          :   						      %
%       (Term,Ty,Mod)     :   Display the lambda Prolog term and its type.    %
%                                                                             %
%   write_term_lp_with_types :   Display a lambda Prolog term with types. Types  %
%              (Term,Mod) :   annotate only the first occurrence of a variable%
%                                                                             %
%   write_subs(Subs,Mod)  :   Display a substitution as columns of Var = Term %
%                                                                             %
%   write_pair(Pair,Mod)  :   Display a (disagreement) pair of terms.         %
%                                                                             %
%                                                                             %
%                                                                             %
%   write_node(Dplist,Mod):   Display a list of disagreement pairs            %
%                                                                             %
%   write_module(Mname)   :   Display a lambda Prolog module.                 %
%                                                                             %
%   write_paths(Paths)    :   Displays a list of module directories           %
%                                                                             %
%   write_goal            :   Print out the Goal declaring Uvars as its       %
%      ([Modules,Uvars,Goal],Mod) :   list of universal variables and         %
%				  :   Modules as its current modules          %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic tabset/1.

%  tabset(N) is satisfied when N is the tab setting currently in effect at 
%  the beginning of the line. The first predicate below initialises this to 
%  0, and the remaining predicates are useful for incrementing, decrementing 
%  and writing the tab.                                                      

    tabset(0).

    inctab :- retract(tabset(N)), !, N1 is N+1, assert(tabset(N1)).

    dectab :- retract(tabset(N)), !, N1 is N-1, assert(tabset(N1)).

    newl :- nl, write_tab.

    write_tab :- (tabset(N),! ; N = 0), writeblanks(N).

    writeblanks(0) :- !.
    writeblanks(N) :- write('  '), N1 is N-1, writeblanks(N1).




% Writing a list of tokens as they appear when read.
  write_line([]).
  write_line([X]) :- write(X), !.
  write_line([X|L]) :- write(X),write(' '), !, write_line(L).





%  Writing out types. The main routine is write_type_withnames. Since type
%  variables are represented by Prolog variables, write_type_withnames binds
%  these to printable names. It is necessary to fail, as in write_type, to undo
%  these bindings. The last argument of write_type_withnames is for determining
%  whether parantheses are necessary. Use 0 if they are necessary in the 
%  context of invocation, and 3 if they are not.  

  write_type(Type) :- write_type_withnames(Type,1,_,3), fail.
  write_type(Type).

  write_type_withnames(Type,Cin,Cout,_) :-
	var(Type), !,
	append_names('A',Cin,VarName), Type = VarName, write(VarName), 
	Cout is Cin + 1, !.
  write_type_withnames(T1 ---> T2,Cin,Cout,Prec) :-
	!, 
	(2 < Prec ; write('(')), 
	write_type_withnames(T1,Cin,Ctmp,2), write(' ---> '),
	write_type_withnames(T2,Ctmp,Cout,3), 
	(2 < Prec ; write(')')), 
	!.
  write_type_withnames(T1 ^ T2,Cin,Cout,Prec) :-
        !,
	(0 < Prec ; write('(')), 
	write_type_withnames(T1,Cin,Ctmp,1), write(' '),
	write_type_withnames(T2,Ctmp,Cout,0),
	(0 < Prec ; write(')')),
	!.
  write_type_withnames(Type,Cin,Cin,_) :-  write(Type),!.





%  Displaying a lambda Prolog term. The routines are complicated since they
%  obey operator declarations, and try to omit parantheses whenever possible.
%  The routines are in two categories, one for writing a term without types 
%  and one for writing a term with types; although the control structure of 
%  these routines is almost identical, it was thought better to separate them 
%  out because there would be a lot of unnecessary computation (unification) 
%  in the more common case, i.e. when types are not needed.                  

  write_term_lp(Term,Mod) :- 
	(printtypes, write_term_lp_with_types(Term,Mod) ; 
	 write_term_lp(Term,Mod,512,_) ), !.

  write_tyterm(Term,Type,Mod) :-  
   (retract(printtypes),
       write_term_lp(Term,Mod),write(' : '),write_type(Type), assert(printtypes) ;
    write_term_lp(Term,Mod), write(' : '), write_type(Type)).
		    

  write_term_lp_with_types(Term,Mod) :-
	(write_term_lp_with_types(Term,Mod,512,_,[],_,1,_), fail ;
	 true), !.


%  The main routine for the case when types are not to be displayed with 
%  the term. Displaying is always done in the context of a module, used for 
%  determining the constants that are to be construed as operators. The third 
%  argument is the `precedence' of the `outer' operator and the last argument
%  tells whether the current term appears to its right or to its left; these
%  together determine when parantheses are needed.                          
   
% When there is a top-level infix operator
  write_term_lp(cv(Tok,Ty,c) ^ Arg1 ^ Arg2,Mod,Prec,LR) :-
	oper_instance(Mod,infix,Prec1,Tok,Mode), !,
	infix_prec(Mode,Prec1,LPrec,RPrec), 
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_term_lp(Arg1,Mod,LPrec,left), 
	write(' '), write_token(cv(Tok,Ty,c)), write(' '),
	write_term_lp(Arg2,Mod,RPrec,right), 
	(Paren_Needed = n ; write(')')), !.

% When there is a top-level postfix or prefix operator
  write_term_lp(cv(Tok,Ty,c) ^ Arg,Mod,Prec,LR) :-
	oper_instance(Mod,Fx,Prec1,Tok,Mode),
	(Fx = postfix, !,
		postfix_prec(Mode,Prec1,Prec2),
		((LR = left, (2 * Prec1) < Prec ; Prec2 < Prec), 
							Paren_Needed = n ;
		 Paren_Needed = y),
		(Paren_Needed = n ; write('(')),
		write_term_lp(Arg,Mod,Prec2,left), write(' '), 
		write_token(cv(Tok,Ty,c)),
		(Paren_Needed = n ; write(')')) ;
	 Fx = prefix, !,
		prefix_prec(Mode,Prec1,Prec2),
		((LR = right, (2 * Prec1) < Prec ; Prec2 < Prec), 
							Paren_Needed = n ;
		  Paren_Needed = y),
		(Paren_Needed = n ; write('(')),
		write_token(cv(Tok,Ty,c)), write(' '), 
		write_term_lp(Arg,Mod,Prec2,right), 
		(Paren_Needed = n ; write(')')) ), 
	!.

% Lists are special objects that need to be printed in list notation
  write_term_lp(Cons ^ A ^ B, Mod, _, _) :-
	list_cons(Cons), !, 
	write('['), write_list(Cons ^ A ^ B,Mod,512), write(']'), !.

% Application is left associative and binds tighter than everything except \ 
  write_term_lp(A ^ B,Mod,Prec,LR) :-
	oper_instance(Mod,infix,AppPrec,'^',Mode),
	infix_prec(Mode,AppPrec,LPrec,RPrec),
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_term_lp(A,Mod,LPrec,left),write(' '),write_term_lp(B,Mod,RPrec,right),
	(Paren_Needed = n ; write(')')), !.

% Abstraction is right associative, and binds tighter than everything else
  write_term_lp(A \ B,Mod,Prec,LR) :-
	oper_instance(Mod,infix,AbstPrec,'\\',Mode),
	infix_prec(Mode,AbstPrec,LPrec,RPrec),
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_token(A), write(' \\ '), write_term_lp(B,Mod,RPrec,right),
	(Paren_Needed = n ; write(')')), !.
 
  write_term_lp(Token,Mod,_,_) :- write_token(Token).
  


% Auxiliary procedure for writing out lists
  write_list(Cons ^ A ^ B,Mod,Prec) :-
	(list_nil(B), write_term_lp(A,Mod,Prec,right) ;
	 B = Cons ^ C ^ D, 
	      oper_instance(Mod,infix,Prec1,',',Mode),
	      infix_prec(Mode,Prec1,LPrec,RPrec),
	      write_term_lp(A,Mod,LPrec,left),write(', '),write_list(B,Mod,RPrec);
	 oper_instance(Mod,infix,Prec1,'|',Mode),
	      infix_prec(Mode,Prec1,LPrec,RPrec),
	      write_term_lp(A,Mod,LPrec,left), write(' | '),
	      write_term_lp(B,Mod,RPrec,right)),
	!.


% Auxiliary procedure for printing out a lambda Prolog token
  write_token(cv(Tok,Ty,c)) :- 
	stringtype(Ty1), Ty == Ty1, !, write(''''), write(Tok), write(''''), !.
  write_token(Nil) :- list_nil(Nil), !, write('[]').
  write_token(cv(Tok,_,_))    :- !, write(Tok).
% These little beasts can occur in the functional interpreter.
  write_token(suspend(_,_))   :- !, write(' *suspend* ').
  write_token(closure(_,_))   :- !, write(' *closure* ').
  write_token(special(_,_,_)) :- !, write(' *special* ').

  

% Converting precedence and mode into (a pair of) single numbers
  infix_prec(Mode,Prec,LPrec,RPrec) :- 
	(Mode = xfx, LPrec is 2 * Prec, RPrec is 2 * Prec ;
	 Mode = xfy, LPrec is 2 * Prec, RPrec is (2 * Prec) +1 ;
	 Mode = yfx, LPrec is (2 * Prec) + 1, RPrec is 2 * Prec ;
	 Mode = yfy, LPrec is (2 * Prec) + 1, RPrec is (2 * Prec) + 1), !.

  postfix_prec(Mode,Prec1,Prec2) :- 
	(Mode = xf, Prec2 = Prec1 ; Mode = yf, Prec2 is (2 * Prec1) + 1), !.

  prefix_prec(Mode,Prec1,Prec2) :- 
	(Mode = fx, Prec2 = Prec1 ; Mode = fy, Prec2 is (2 * Prec1) + 1), !.





%  A set of routines exactly analogous to those above, except that types are
%  also printed out. The last two arguments are `counter' numbers at entry 
%  and exit used in converting type variables into printable names. The 5th
%  and 6th arguments maintain variable lists used to determine when types
%  must be printed.                                                         

  write_term_lp_with_types(cv(Tok,Ty,c)^A^B,Mod,Prec,LR,Vl,NVl,Cin,Cout) :-
	oper_instance(Mod,infix,Prec1,Tok,Mode), !,
	infix_prec(Mode,Prec1,LPrec,RPrec), 
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_term_lp_with_types(A,Mod,LPrec,left,Vl,TVl,Cin,Ctmp), 
	write(' '), 
	write_token_with_types(cv(Tok,Ty,c),TVl,TVl,Ctmp,Ctmp), 
	write(' '),
	write_term_lp_with_types(B,Mod,RPrec,right,TVl,NVl,Ctmp,Cout), 
	(Paren_Needed = n ; write(')')), !.

  write_term_lp_with_types(cv(Tok,Ty,c)^Arg,Mod,Prec,LR,Vl,NVl,Cin,Cout) :-
	oper_instance(Mod,Fx,Prec1,Tok,Mode),
	(Fx = postfix, !,
		postfix_prec(Mode,Prec1,Prec2),
		((LR = left, (2 * Prec1) < Prec ; Prec2 < Prec), 
							Paren_Needed = n ;
		 Paren_Needed = y),
		(Paren_Needed = n ; write('(')),
		write_term_lp_with_types(Arg,Mod,Prec2,left,Vl,NVl,Cin,Cout), 
		write(' '), write_token(cv(Tok,Ty,c)),
		(Paren_Needed = n ; write(')')) ;
	 Fx = prefix, !,
		prefix_prec(Mode,Prec1,Prec2),
		((LR = right, (2 * Prec1) < Prec ; Prec2 < Prec), 
							Paren_Needed = n ;
		  Paren_Needed = y),
		(Paren_Needed = n ; write('(')),
		write_token(cv(Tok,Ty,c)), write(' '), 
		write_term_lp_with_types(Arg,Mod,Prec2,right,Vl,NVl,Cin,Cout), 
		(Paren_Needed = n ; write(')')) ), 
	!.

  write_term_lp_with_types(Cons ^ A ^ B, Mod, _, _,Vl,NVl,Cin,Cout) :-
	list_cons(Cons), !, 
	write('['), 
	write_list_with_types(Cons ^ A ^ B,Mod,512,Vl,NVl,Cin,Cout), 
	write(']'), !.

  write_term_lp_with_types(A ^ B,Mod,Prec,LR,Vl,NVl,Cin,Cout) :-
	oper_instance(Mod,infix,AppPrec,'^',Mode),
	infix_prec(Mode,AppPrec,LPrec,RPrec),
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_term_lp_with_types(A,Mod,LPrec,left,Vl,TVl,Cin,Ctmp),
	write(' '),
	write_term_lp_with_types(B,Mod,RPrec,right,TVl,NVl,Ctmp,Cout),
	(Paren_Needed = n ; write(')')), !.

  write_term_lp_with_types(A \ B,Mod,Prec,LR,Vl,NVl,Cin,Cout) :-
	oper_instance(Mod,infix,AbstPrec,'\\',Mode),
	infix_prec(Mode,AbstPrec,LPrec,RPrec),
	((LR = left, RPrec < Prec ; LPrec < Prec), Paren_Needed = n ;
	 Paren_Needed = y),
	(Paren_Needed = n ; write('(')), !,
	write_token_with_types(A,[],_,Cin,Ctmp), write(' \\ '), 
	write_term_lp_with_types(B,Mod,RPrec,right,[A|Vl],NVl,Ctmp,Cout),
	(Paren_Needed = n ; write(')')), !.
 
  write_term_lp_with_types(Token,Mod,_,_,Vl,NVl,Cin,Cout) :- 
				write_token_with_types(Token,Vl,NVl,Cin,Cout).





  write_list_with_types(Cons ^ A ^ B,Mod,Prec,Vl,NVl,Cin,Cout) :-
	(list_nil(B), write_term_lp_with_types(A,Mod,Prec,right,Vl,NVl,Cin,Cout) ;
	 B = Cons ^ C ^ D, 
		oper_instance(Mod,infix,Prec1,',',Mode),
		infix_prec(Mode,Prec1,LPrec,RPrec),
		write_term_lp_with_types(A,Mod,LPrec,left,Vl,TVl,Cin,Ctmp),
		write(', '), 
		write_list_with_types(B,Mod,RPrec,TVl,NVl,Ctmp,Cout) ;
	 oper_instance(Mod,infix,Prec1,'|',Mode),
		infix_prec(Mode,Prec1,LPrec,RPrec),
		write_term_lp_with_types(A,Mod,LPrec,left,Vl,TVl,Cin,Ctmp),
		write(' | '),
		write_term_lp_with_types(B,Mod,RPrec,right,TVl,NVl,Ctmp,Cout)),
	!.



%  Auxiliary procedure for printing out a lambda Prolog token. Only variables 
%  have their types displayed, and, that too, only at their first
%  occurrence.

  write_token_with_types(cv(Tok,Ty,c),Vl,Vl,Cin,Cin) :- 
	stringtype(Ty1), Ty == Ty1, !, write(''''), write(Tok), write(''''), !.
  write_token_with_types(Nil,Vl,Vl,Cin,Cin) :- list_nil(Nil), !, write('[]').
  write_token_with_types(cv(Tok,_,c),Vl,Vl,Cin,Cin) :- write(Tok).
  write_token_with_types(cv(Tok,Ty,v),Vl,NVl,Cin,Cout) :-
	(lp_member(cv(Tok,Ty,v),Vl), !, NVl = Vl, write(Tok), Cin = Cout ;
	 NVl = [cv(Tok,Ty,v)|Vl], 
		write(Tok), write(' : '), write_type_withnames(Ty,Cin,Cout,3)
	),
	!.
% These little beasts can occur in the functional interpreter.
  write_token_with_types(suspend(_,_))   :- !, write(' *suspend* ').
  write_token_with_types(closure(_,_))   :- !, write(' *closure* ').
  write_token_with_types(special(_,_,_)) :- !, write(' *special* ').



%  Displaying various kinds of data structures whose components are lambda
%  Prolog terms. These basically build on write_term_lp defined above. 

% Displaying a substitution; the first element of a pair is the variable
  write_subs([],_) :- !.
  write_subs([[Var,Term]|Subs],Mod) :-
	nl, write_token(Var),  write(' = '), write_term_lp(Term,Mod),
	write_subs(Subs,Mod), !.

% Displaying a disagreement pair
  write_pair([Term1,Term2],Mod) :-
	write('<'), 
	write_term_lp(Term1,Mod),  write(' , '), write_term_lp(Term2,Mod), 
	write('>'), !.

  write_term_lplist([],_) :- !.
  write_term_lplist([Term|Terms],Mod) :-  
		nl, write_term_lp(Term,Mod), !, write_term_lplist(Terms,Mod).

% Displaying a list if disagreement pairs; note that there is an initial nl.
   write_node([],_) :- !.
   write_node([Pair|Node],Mod) :-
        !, nl, write_pair(Pair,Mod), write_node(Node,Mod).





% Displaying the various declarations in a module. 
  write_module(Module) :-
	write('    module '), write(Module), write('.'), nl,
	write_import_dec(Module),
	write_op_dec(Module),
	write_kind_dec(Module),
	write_type_dec(Module),
	write_expression_dec(Module),
	write_clause_dec(Module),
	nl, !.

  write_import_dec(Module) :-
	import(Module,ImTemp),
	(ImTemp = [sys_defs|Im] ; Im = ImTemp), !,
	(Im=[] ; write('    import '), write_line(Im), write('.'), nl), !.
  write_import_dec(_).

  write_op_dec(Module) :-
	operator(Module,Fx,Priority,Op,Mode),
	write('    '), write(Fx), write(' '), write(Priority), write(' '),
	write(Op), write(' '), write(Mode), write('.'), nl, fail.
  write_op_dec(_).

  write_kind_dec(Module) :-
	kind(Module,Tok,Kind), write('    kind '), 
	write(Tok), write(' '), write_type(Kind), write('.'), nl, fail.
  write_kind_dec(_).

  write_type_dec(Module) :-
	type(Module,Tok,Type), write('    type '), 
	write(Tok), write(' '), write_type(Type), write('.'), nl, fail.
  write_type_dec(_).

  write_expression_dec(Module) :-
	expression(Module,Name,Exp), write('    exp '), write_token(Name), 
	write('    '), write_term_lp(Exp,Module), write('.'), nl, fail.
  write_expression_dec(_).

  write_clause_dec(Module) :-
	lp_clause(Module,Pred,Clause), write('    '),
	write_term_lp(Clause,Module), write('.'), nl, fail.
  write_clause_dec(_).



write_paths([]).
write_paths([Path|Restpaths]) :-
    !, writeblanks(2), write(Path), nl, write_paths(Restpaths).


write_goal([Modules,Uvars,Goal],Mod) :-
    write('Modules:  '), write_mods(Modules), nl,
    (Uvars=[],! ;
     write('Uvars:    '), write_Uvars(Uvars,Mod),nl),
    write_term_lp(Goal,Mod).


%  If we only had higher-order features!!
write_mods([]).
write_mods([M|L]) :- write(M), write(' '), write_mods(L).

write_Uvars([],_).
write_Uvars([Uvar|L],Mod) :- write_term_lp(Uvar,Mod), write(' '), write_Uvars(L,Mod).


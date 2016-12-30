  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                                                                             %
%                              FILE  PARSER.PL                                %
%                            -------------------                              %
%                                                                             %
%    The clauses in this file define a parser for the declarations that occur %
%    in the body of a module. If a declaration is parsed successfully then it %
%    leaves a trace in a side-effect. The side effects that might occur       %
%    consist of some of the following facts  being asserted:                  %
%                                                                             %
%                                                                             %
%             import(Mname,Modlist)                                           %
%             operator(Mname,Fix,Priority,Op,Mode)                            %
%             kind(Mname,Tok,Kind)                                            %
%             type(Mname,Tok,Type)                                            %
%             expression(Mname,Tok,Term)                                      %
%             lp_clause(Mname,Pred,Clause)                                    %
%                                                                             %
%                                                                             %
%    The declarations that occur in a module are assumed to be arranged in    %
%    the following order                                                      %
%			     module   <module name> 			      %
%			       <op declarations>                              %
%			      <kind declarations>			      %
%			      <type declarations>			      %
%		     <clauses and function definitions>			      %
%                                                                             %
%    parse_modname below is responsible for parsing module name declarations. %
%    The remaining declarations are parsed by parse_modbody. This predicate   %
%    is invoked in a particular state, and attempts to parse the input line   %
%    in that state. In this attempt, it invokes op_dec, kind_dec, type_dec    %
%    or clause_and_exp_dec depending on the state it is in. The first three   %
%    of these are actually invoked via parse_line which actually fails when   %
%    a parse is successful --- thereby causing a backtrack and a retrial on   %
%    a new line --- and succeeds returning the next state when a parse is     %
%    unsuccessful. This curious structure is necessary to provide a parser    %
%    that is for the large part iterative and not recursive. The only         %
%    exception to this structure is when the state is clause_and_exp_dec, in  %
%    which case there is never a failure. This is so because this is the      %
%    last state and a failure to parse the line should really lead to an      %
%    error massage, and not to an attempt to retry the same line in a new     %
%    state.          							      %
%									      %
%    The only other general point to note with regard to the parsing rout-    %
%    ines here is that they expect the end of file to be signalled by an      %
%    empty line being returned by the scanner.				      %
%                                                                             %
%    This file requires predicates defined in the files                       %
%           (i) errors.pro (for the error routines)                           %
%          (ii) scanner.pro (the predicate read_line)                         %
%         (iii) terms.pro   (is_var, same_name_occurs, and head_of_clause)    %
%          (iv) modules.pro (the predicate load_modules)                      %
%                                                                             %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



  :- dynamic operator/5, kind/3, type/3, expression/3, lp_clause/3.

% Predicates for determining whether a token read in is a token of some 
%  special kind. 

% Is a given token a symbol that represents a variable?
     var_token(Tok) :-  atomic(Tok), name(Tok,[X|L]), !, 64 < X, !, X < 91.

% Is a given token a symbol that represents a constant?
     constant_token(Tok) :- atomic(Tok), name(Tok,[X|L]), (X < 65 ; 90 < X).

% Is a given token a symbol that corresponds to a string?
%     string(X) :- quote(Quote), name(X,[Quote|_]).

% Is a given token a symbol that has a special significance?
     special_symbol(X) :- 
		(X = '(' ; X = ')' ; X = '.' ; (X = '\\') ; 
		 X = ':' ; X = ('--->') ; X = '[' ; X = ']' ; X = '|'), !.




%  Some DCG rules useful in most of the rules that follow

% Is the next object in the input a token that does not have a special meaning?
 token(_) --> [X],{special_symbol(X), !, fail}.
 token(X) --> [X], {atomic(X),!}.

% token_list returns the list of tokens that follow in the input line
 token_list([Tok|Tokens]) --> token(Tok),{!},token_list(Tokens).
 token_list([]) --> [].

%  Flushing the input line on an error. Necessary for successful termination of
%  DCG rule after the error is indicated.

 flush_input --> [X], {!}, flush_input.
 flush_input --> [].




% Parsing the module name declaration. parse_modname indicates an error if
%  the module name is not defined or if it is different from the expected one.
%  Parsing is continued assuming that the expected name is the right one.

 parse_modname(Mname,Line) --> 
     ([module],
            (token(Mname),
                 (['.'], ! ;
                  flush_input, {syntax_error(delimiter,'.',Line),!});
             flush_input, {syntax_error(moddec,name,Mname,Line),!});
      flush_input, {syntax_error(moddec,name,none,Line)}).




%   parse_modbody(Mod,State,Line) parses the remaining declarations in the
%   module. State determines what kind of declaration is expected. An attempt
%   is made to parse the current line in State. A successful parse in State
%   causes the next line to be read and the process to be repeated. A failure
%   causes the State to be `advanced' and parse_modbody to be invoked on Line 
%   in the new State; next_parse_state(State,Newstate) is used to determine 
%   the next state. There is a final state, currently clause_and_exp_dec, that
%   is an exception in that failure to parse Line in that state does not ever
%   cause a failure. 
%   The structure of the parser is such that it is provided with an entire
%   lp line upon entry through the argument Line. An end of file condition is
%   signalled by instantiating Line to [].

 parse_modbody(Mname,State,Line) :- 
     (State = clause_and_exp_dec, !, parse_ce_decs(Mname,Line,[],[]);
      (Line = [], !;
        (parse_dec(Mname,State,Line), !,
           repeat, read_line(Newline),
                   parse_line(Mname,State,Newline,Newstate),!;
         Newline = Line, next_parse_state(State,Newstate)),
        parse_modbody(Mname,Newstate,Newline))).





%  predicate to indicate the next state for the parser
 next_parse_state(import_dec,op_dec).
 next_parse_state(op_dec,kind_dec).
 next_parse_state(kind_dec,type_dec).
 next_parse_state(type_dec,clause_and_exp_dec).




%  parse_line(Mname,State,Line,Newstate) FAILS every time it Line is to be 
%  parsed in State, and succeeds when Line is [] or should not be parsed in
%  State. In the latter case Newstate indicates the next state in which an
%  attempt to parse Line should be made.

 parse_line(_,_,[],_) :- !.
 parse_line(Mname,State,Line,_)  :- parse_dec(Mname,State,Line), !, fail.
 parse_line(_,State,_,Newstate)  :- next_parse_state(State,Newstate).




% Invoking the right DCG rule to attempt to parse Line in State
     parse_dec(Mname,State,Line) :-
               P =.. [State,Mname,Line,Line,[]], call(P).




%  Invoking the DCG rule to parse clause or function definitions. A desire to
%  infer the most general type that satisfies typing constraints for constants
%  precludes the use of a completely iterative version of parse_modbody.
%  Consequently this separate tail recursive part.

 parse_ce_decs(Mname,Line,Cl,Expl) :-
     (Line = [], !, assert_type_dec(Mname,Cl), assert_clause_dec(Mname,Expl) ;
      clause_and_exp_dec(Mname,Line,Cl,NCl,Expl,NExpl,Line,[]), 
                   read_line(Newline), parse_ce_decs(Mname,Newline,NCl,NExpl)).


        

% Leaving a trace of the types inferred for constants in a module.
  assert_type_dec(Mname,[]).
  assert_type_dec(Mname,[cv(Tok,Type,c)|Clist]) :-
            assertz(type(Mname,Tok,Type)), assert_type_dec(Mname,Clist).




% Relp_membering the clauses defined in a module
  assert_clause_dec(Mname,[]).
  assert_clause_dec(Mname,[X|Clist]) :-
            asserta(X), assert_clause_dec(Mname,Clist).






%                    PARSING AN IMPORT DECLARATION

 import_dec(Mname,Line) --> 
        [import], 
        (token_list(ModLst), 
           (['.'], {check_importlist(Mname,ModLst,MLst,Line), 
			add_to_importlist(Mname,MLst),
			add_mlinks(Mname,MLst), load_modules(MLst), !};
            flush_input, {syntax_error(delimiter,'.',Line), !});
         flush_input, {syntax_error(impdec,implist,Line), !}).



  check_importlist(Mname,[],[],_) :- !.
  check_importlist(Mname,[X|RestIn],RestOut,Line) :-
	path_exists(Mname,X), !,
	syntax_error(impdec,cycle,Mname,X,Line),
	check_importlist(Mname,RestIn,RestOut,Line), !.
  check_importlist(Mname,[X|RestIn],[X|RestOut],Line) :-
		check_importlist(Mname,RestIn,RestOut,Line), !.



% Relp_membering the names of modules imported
 add_mlinks(M,[]).
 add_mlinks(M,[N|L]) :- assertz(mlink(M,N)), add_mlinks(M,L).



 add_to_importlist(Mname,Modlist) :-
                     (retract(import(Mname,Modl)) ; Modl = []),
                     join(Modl,Modlist,NModl), assert(import(Mname,NModl)),!.


% Links between modules that come into effect as a result of importation
   path_exists(To,To) :- !.
   path_exists(To,From) :- mlink(M,To), path_exists(M,From),!.




%                 PARSING AN OPERATOR DECLARATION    

 op_dec(Mname,Line) --> 
        [X], {(X = infix; X = prefix; X = postfix)},
        (pnumber(Priority),
           (token(Op),
              (mode(X,Mode),
                  (['.'],{assertz(operator(Mname,X,Priority,Op,Mode)),!};
                   flush_input, {syntax_error(delimiter,'.',W), !});
               flush_input, {syntax_error(opdec,(mode),X,Line), !});
             flush_input, {syntax_error(opdec,opname,Line), !});
         flush_input, {syntax_error(opdec,priority,Line)}).



% Is the next object in the input is a valid priority declaration?
 pnumber(N) --> [N],{integer(N),0<N,N<256, !}.


% Is next input token a valid mode declaration for an operator of given kind?
 mode(infix,X) --> [X], {(X = xfy ; X = yfx ; X =xfx ; X = yfy), !}.
 mode(prefix,X) --> [X], {(X = fx ; X = fy), !}.
 mode(postfix,X) --> [X], {(X = yf ; X = xf), !}.






%                   PARSING A KIND DECLARATION 

 kind_dec(Mname,Line) --> 
     [kind],
     (token(Tok), parse_kind(Mname,Kind,[],[],Line,Err),
          ({Err = true, !}, flush_input;
             (['.'], {assertz(kind(Mname,Tok,Kind)), !};
              flush_input, {syntax_error(delimiter,'.',Line), !}));
      flush_input, {syntax_error(kinddec,name,Line)}).



%  Parsing a kind expression. If the following objects, upto a special symbol,
%  in the input constitute a valid kind expression, then Kind is bound to the
%  internal representation of that expression. Otherwise Err is bound to true.
%  KiTS and KiOS are kind term and operator stacks used in the process.

 parse_kind(Mname,Kind,KiTS,KiOS,Line,Err) -->
	[--->],
	({(KiTS = [] ; KiOS = [[--->,targ]|_]),
                  Err = true, syntax_error(kinddec,kind,fn,domain,none,Line)} ;
	  parse_kind(Mname,Kind,KiTS,[[--->,targ]|KiOS],Line,Err)),
	{!}.

 parse_kind(Mname,Kind,KiTS,KiOS,Line,Err) -->
	token(Sy),
	({Sy = type},
		({(KiTS = [], NKiOS = KiOS ; 
		   KiOS = [[--->,targ]|L], NKiOS = [--->|L])},
		           parse_kind(Mname,Kind,[Sy|KiTS],NKiOS,Line,Err) ;
		 {Err = true, syntax_error(kinddec,kind,appl,Sy,Sy1,Line)}) ;
	 {Err = true, syntax_error(kinddec,kind,token,X,Line)}),
	{!}.

parse_kind(Mname,Kind,KiTS,KiOS,Line,Err) -->
	[], {make_kind(Kind,KiTS,KiOS,Line,Err), !}.





% Collapsing the token and operator stacks to form a kind expression
   make_kind(Kind,[],_,Line,true) :-
                        syntax_error(kinddec,kind,none,Line), !.
   make_kind(_,_,[[--->,targ]|L],Line,true) :-
                        syntax_error(kinddec,kind,fn,range,none,Line), !.
   make_kind(Kind,KiTS,KiOS,Line,false) :-
                        make_kind1(Kind,KiTS,KiOS).

   make_kind1(Kind,[Kind],_).
   make_kind1(Kind,[X,Y|L],[--->|K]) :- make_kind1(Kind,[Y ---> X|L],K).






%                    PARSING A TYPE DECLARATION  

 type_dec(Mname,Line) --> 
	[type],
	(token(Tok),
		parse_type(Mname,TyKi,[],[],[],_,Line,Err),
		({Err = true}, flush_input ;
		   (['.'], {TyKi = [Type,type], assertz(type(Mname,Tok,Type))};
		    flush_input, {syntax_error(delimiter,'.',Line)})) ;
	 flush_input, {syntax_error(typedec,name,Line)}), {!}.



%  Parsing a type expression. It is assumed that as large a portion of the
%  input as is possible is to be used in this pursuit. If a valid type 
%  expression is found, the second argument is bound to an internal 
%  representation of it. Otherwise an error is indicated by binding the last 
%  argument to true. The third and fourth arguments are 'term' and 'operator'
%  stacks used in the process. The fifth and sixth arguments are used for 
%  keeping track of the type variables encountered; this is necessary to 
%  ensure the correct quantificational interpretation of such variables, i.e.
%  implicit universal quantification over the whole expression. 

 parse_type(Mname,Ty,TyTS,TyOS,Vl,NVl,Line,Err) -->
	['--->'],
	({(TyTS = [] ; TyOS = [[--->,targ]|_]),
                syntax_error(typedec,type,fn,domain,none,Line), Err = true} ;
	 {TyTS = [[Ty1,Kind]|_]},
	  ({Kind = type},
		 parse_type(Mname,Ty,TyTS,[[--->,targ]|TyOS],Vl,NVl,Line,Err) ;
	   {syntax_error(typedec,type,fn,domain,kind,Ty1,Kind,Line),Err = true}
	   )
	), {!}.

 parse_type(Mname,Ty,TyTS,TyOS,Vl,NVl,Line,Err) -->
	{(TyTS = [] ; TyTS = [[_,K1 ---> K2]|_] ; TyOS = [[--->,targ]|_])},
	{!},
	((['('], parse_type(Mname,SubTy,[],[],Vl,TVl,Line,Suberr),
		 ({Suberr = true, Err = true} ;
		  [')'] ;
		  {syntax_error(delimiter,')',Line), Err = true}) ;
	  type_token(Mname,SubTy,Vl,TVl)),
		({Err == true} ;
	         {stack_type_term(SubTy,TyTS,TyOS,TTyTS,TTyOS)},
			parse_type(Mname,Ty,TTyTS,TTyOS,TVl,NVl,Line,Err)) ;
	 {Err = true,
	   (TyTS = [], syntax_error(typedec,type,none,Line) ;
	    TyOS = [[--->|targ]|_],
			     syntax_error(typedec,type,fn,range,none,Line) ;
	    TyTS = [[Ty,Kind]|_], syntax_error(typedec,type,kind,Ty,Kind,Line) 
	   )}
	), {!}.

 parse_type(Mname,Ty,TyTS,TyOS,Vl,Vl,Line,Err) -->
	{(TyOS = [[--->,targ]|_], Err = true,
			syntax_error(typedec,type,fn,range,none,Line) ;
	  Err = false, make_type(Ty,TyTS,TyOS)), 
	 !}.




%  Parsing a type token. A kind and an internal representation is returned.
%  Tokens whose kinds are not defined are inferred to have the kind TYPE. 

  type_token(Mname,[A,Ki],Vl,NVl) -->
	token(Sy),
	{(var_token(Sy), Ki = type,
		(lp_member([Sy,A],Vl), NVl = Vl ; NVl = [[Sy,A]|Vl]) ;
	  A = Sy, NVl = Vl, (kind_instance(Mname,Sy,Ki) ; Ki = type)), !}.



kind_instance(Module,Tok,Kind) :- kind(Module,Tok,Kind), !.
kind_instance(Module,Tok,Kind) :- 
	!, mlink(Module,Mod), kind_instance(Mod,Tok,Kind), !.




%  Modifying the term and operator stacks when a type term is parsed

  stack_type_term(SubTy,TyTS,TyOS,TTyTS,TTyOS) :-
	 (TyTS = [], TTyTS = [SubTy|TyTS], TTyOS = TyOS ;
	  TyOS = [[--->,targ]|L], TTyOS = [--->|L], TTyTS = [SubTy|TyTS] ;
	  TyTS = [[Ty1,K2 ---> K1]|L], SubTy = [Ty2,K2], 
				TTyTS = [[Ty1 ^ Ty2,K1]|L], TTyOS = TyOS).




% Collapsing the type token and operator stacks to form a type expression

    make_type(Ty,[Ty],[]) :- !.
    make_type(Ty,[[X,_],[Y,_]|RTyTS],[--->|RTyOS]) :-
			!, make_type(Ty,[[Y ---> X,type]|RTyTS],RTyOS).







%                 PARSING A CLAUSE OR EXPRESSION DECLARATION

%   Note: This DCG rule succeeds whenever it is invoked. Failure in parsing is
%  indicated only as a syntax error.

%  The keyword EXP signals an expression declaration  
 clause_and_exp_dec(Mname,Line,Cl,NCl,Expl,NExpl) --> 
   [exp],
   (cv_symbol(Mname,[Tok,Ty],[],TyVl,Line,TyErr1), 
	({TyErr1 = true}, flush_input ;
	 {is_param(Tok), !},
	    {check_type_constraints(Mname,Tok,Cl,TCl,Vl,TVl,Line,TyErr2)},
	    ({TyErr2 = true}, flush_input ; 
	     parse_term(Mname,'.',TyTerm,[],[],TCl,NCl,[],NVl,TyVl,_,Line,Err),
	       {(Err = true ;
                 TyTerm = [Term,Ty], NExpl = [expression(Mname,Tok,Term)|Expl];
                 syntax_error(cande_dec,exp,binding,Tok,Ty,Term,Ty1,Mname,Line)
                )})) ;
    flush_input, {syntax_error(cande_dec,exp,tokenname,Line),!}), 
   {!}.

% Anything else must be a clause declaration
 clause_and_exp_dec(Mname,Line,Cl,NCl,Expl,NExpl) -->
   parse_term(Mname,'.',TTerm,[],[],Cl,NCl,[],NVl,[],_,Line,Err),
   {(Err = true ;
     TTerm = [Term,Ty],
	(Ty = o, 
	  (head_of_clause(Term,HeadPred),
                 NExpl = [lp_clause(Mname,HeadPred,Term) | Expl] ;
           syntax_error(cande_dec,clause,head,Line)) ;
         syntax_error(cande_dec,clause,notclause,Ty,Line))), !}.
     



%  Parsing a lambda-Prolog term. If the token in the input upto a token equal
%  to the second argument of parse_term form a valid lambda-Prolog term, then
%  the third argument is bound to a `pair' consisting of the internal repre-
%  sentation of this term and its type. Otherwise the last argument is bound
%  to true. The technique for parsing utilises standard techniques for parsing 
%  expressions with infix and postfix operators. The 4th and 5th arguments 
%  are the term and operator stacks used in this process. The next two 
%  arguments are used to relp_member the constants encountered in the term and 
%  their types constraints. The next two arguments are used to relp_member
%  variables encountered, so as to capture their implicit universal quantifi-
%  cation over the entire term. Finally, the 10th and 11th arguments provide
%  the necessary bookkeeping to ensure that variables in type expressions
%  provided within a term are quantified over the entire term.

 parse_term(Mod,EOT,TTerm,TS,OS,Cl,NCl,Vl,NVl,TyVl,NTyVl,Line,Err) -->
	(['('],            % a subexpression
	   parse_term(Mod,')',Term,[],[],Cl,TCl,Vl,TVl,TyVl,TTyVl,Line,Suberr);
	 ['['],            % a list expression
	   parse_term(Mod,']',Term,[],[],Cl,TCl,Vl,TVl,TyVl,TTyVl,Line,Suberr)
	),
	({Suberr = true, Err = true}, flush_input ;
	 {stack_term(Mod,Term,TS,OS,NTS,NOS,TCl,TTCl,TVl,TTVl,Line,Stkerr)},
	    ({Stkerr = true, Err = true}, flush_input ;
             parse_term(Mod,EOT,TTerm,NTS,NOS,TTCl,NCl,
					TTVl,NVl,TTyVl,NTyVl,Line,Err) ) ),
       {!}.

 parse_term(Mod,EOT,TTerm,TS,OS,Cl,NCl,Vl,NVl,TyVl,NTyVl,Line,Err) -->
	op_symbol(Mod,Op),
	{!, stack_op(Mod,Op,TS,OS,NTS,NOS,Cl,TCl,Vl,TVl,Line,Stkerr)},
	({Stkerr = true, Err = true}, flush_input;
	 parse_term(Mod,EOT,TTerm,NTS,NOS,TCl,NCl,TVl,NVl,TyVl,NTyVl,Line,Err)
	), {!}.

 parse_term(Mod,EOT,TTerm,TS,OS,Cl,NCl,Vl,NVl,TyVl,NTyVl,Line,Err) -->
	cv_symbol(Mod,Tok_Ty,TyVl,TTyVl,Line,TyErr), 
	{!},
	({TyErr = true} ;
	 {stack_term(Mod,Tok_Ty,TS,OS,NTS,NOS,Cl,TCl,Vl,TVl,Line,Stkerr)},
		({Stkerr = true, Err = true}, flush_input;
		 parse_term(Mod,EOT,TTerm,NTS,NOS,TCl,NCl,
			    TVl,NVl,TTyVl,NTyVl,Line,Err)
		)
	),
	{!}.

 parse_term(Mod,EOT,TTerm,TS,OS,Cl,NCl,Vl,NVl,TyVl,TyVl,Line,Err) -->
	[EOT], 
	{(EOT = ']',
		make_list(Mod,TS,OS,TTerm,Cl,NCl,Vl,NVl,Line,Err) ;
	  make_term(Mod,TS,OS,TTerm,Cl,NCl,Vl,NVl,Line,Err)), !}.

 parse_term(_,EOT,_,_,_,_,_,_,_,TyVl,TyVl,Line,true) --> 
	flush_input, {syntax_error(delimiter,EOT,Line), !}.

% Parsing an token that is a defined operator
 op_symbol(Mod,op(Tok,Fix,P,Mode)) -->
	[Tok], {oper_instance(Mod,Fix,P,Tok,Mode), !}.



 oper_instance(_,infix,-1,'^',yfx) :- !.
 oper_instance(_,infix,253,'|',xfy) :- !. 
 oper_instance(_,infix,-2,'\\',xfy) :- !.
% Before looking carefully through the mlink graph for an operator 
% declaration, check first it some declaration exists anywhere.
 oper_instance(Module,Fix,Priority,Op,Mode) :-
	      (operator(_,_,_,Op,_),!,
	        oper_find(Module,Fix,Priority,Op,Mode) ; fail).
 oper_find(Module,Fix,Priority,Op,Mode) :-
              operator(Module,Fix,Priority,Op,Mode), !.
 oper_find(Module,Fix,Priority,Op,Mode) :-
	!, mlink(Module,Mod), oper_find(Mod,Fix,Priority,Op,Mode), !.




% Parsing a token that is a lambda Prolog constant or variable
 cv_symbol(Mod,[cv(Sy,Ty,CV),Ty],TyVl,NTyVl,Line,Err) -->
	token(Sy1),
	  ({(string(Sy1), lp_remove_quotes(Sy1,Sy), stringtype(Ty) ; 
	     integer(Sy1), Sy = Sy1, integertype(Ty) ), 
					CV = c, Err = false, TyVl = NTyVl} ;
	   {Sy = Sy1, (var_token(Sy), CV = v ; CV = c)},
		([':'], parse_type(Mod,[Ty,type],[],[],TyVl,NTyVl,Line,Err) ;
		 {Err = false, NTyVl = TyVl})),
	{!}.





%          ADDING AN OPERATOR TERM TO THE OPERATOR STACK

%  Only a prefix operator with lower right precedence than that of the top of
%  stack prefix operator is permitted on an empty term stack.

    stack_op(Mod,Op,[],OS,[],NOS,CL,CL,VL,VL,W,Err) :-
          (prefix(Op), Opterm = [pre,Op],
              (OS = [], Err = false, NOS = [Opterm] ;
               OS = [[pre,Op1]|L],
                 (oper_prec(right,right,lower,Op1,Op), 
                                      Err = false, NOS = [Opterm,Op1|L] ;
                  Err = true, syntax_error(term,oper_prec,lower,Op1,Op,W)) );
           Err = true, syntax_error(term,oper_kind,prefix,Op,W)), !.


%  Only prefix operators with lower right precedence may immediately follow
%  an infix or prefix operator.

   stack_op(Mod,Op1,TS,[[Fx,Op2]|ROS],TS,NOS,CL,CL,VL,VL,W,Err) :-
         (prefix(Op1),
            (oper_prec(right,right,lower,Op2,Op1), 
                               Err = false, NOS = [[pre,Op1],Op2|ROS] ;
             Err = true, syntax_error(term,oper_prec,lower,Op2,Op1,W)   );
          Err = true, syntax_error(term,oper_kind,prefixfollow,Op2,W)), !.


%  With a 'fulfilled' operator on top of the operator stack, the incoming 
%  operator may be prefix. In this case an apply must be put in between.

   stack_op(Mod,Op1,TS,OS,NTS,NOS,CL,NCL,VL,NVL,W,Err) :-
        prefix(Op1), apply_op(AppOp),
        stack_op(Mod,AppOp,TS,OS,TTS,TOS,CL,TCL,VL,TVL,W,Stkerr),
        (Stkerr = true, !, Err = true ;
         stack_op(Mod,Op1,TTS,TOS,NTS,NOS,TCL,NCL,TVL,NVL,W,Err)), !.


%  If a postfix operator is on top of the operator stack, the incoming operator
%  may be postfix or infix only if it has higher left precedence.

  stack_op(Mod,Op1,TS,[Op2|ROS],NTS,NOS,CL,NCL,VL,NVL,W,Err) :-
        postfix(Op2), 
        (oper_prec(left,left,higher,Op2,Op1),
                        form_term(Mod,Op2,TS,TTS,CL,TCL,VL,TVL,W,Termerr),
              (Termerr = true, Err = true ;
               stack_op(Mod,Op1,TTS,ROS,NTS,NOS,TCL,NCL,TVL,NVL,W,Err)) ;
         Err = true, syntax_error(term,oper_prec,higher,Op2,Op1,W)), !.


%  If the top of stack infix or prefix operator has lower right precedence than
%  the left precedence of the incoming operator, then shrink the stacks first
%  and then retry stacking the incoming operator.

  stack_op(Mod,Op1,TS,[Op2|ROS],NTS,NOS,CL,NCL,VL,NVL,W,Err) :-
        oper_prec(right,left,higher,Op2,Op1),
        form_term(Mod,Op2,TS,TTS,CL,TCL,VL,TVL,W,Termerr), !,
        (Termerr = true, Err = true ;
         stack_op(Mod,Op1,TTS,ROS,NTS,NOS,TCL,NCL,TVL,NVL,W,Err)), !.


%  If the incoming operator is an abstraction that is to be stacked, then some
%  bookkeeping has to be done to ensure proper scoping.

 stack_op(Mod,Op,[[V,Ty]|L],OS,[[V,Ty]|L],[[in,Op]|OS],CL,CL,VL,[V|VL],W,Err):-
	abst_op(Op),
	(OS = [] ; OS = [Op1|L1], oper_prec(right,left,lower,Op1,Op)),
	(is_var(V), Err = false ; Err = true, syntax_error(term,abst,V,Mod,W)),
	!.

%  Finally, if the incoming operator has lower left precedence than the right
%  precedence of the top of stack operator, stack it in appropriate form.

  stack_op(Mod,Op1,TS,OS,TS,[Opterm|OS],CL,CL,VL,VL,W,Err) :-
       (infix(Op1), Opterm=[in,Op1] ; Opterm = Op1),
       (OS = [], Err = false ;
        OS =[Op2|L],
            (oper_prec(right,left,lower,Op2,Op1), Err = false ;
             Err = true, syntax_error(term,oper_prec,neq,Op2,Op1,W))), !.

   



% Predicates on operators used in stack_op.

% The terms for apply and abstraction as they are stored in the operator stack
   apply_op(op('^',Fix,Prec,Mode)) :- oper_instance(_,Fix,Prec,'^',Mode), !.
   abst_op(op('\\',Fix,Prec,Mode)) :- oper_instance(_,Fix,Prec,'\\',Mode), !.

% Getting the name of the operator from the operator term as stored in the OS
   opname(op(Name,_,_,_),Name).

% Checking if an operator (as stored in the OS) is prefix, infix, or postfix
   prefix(op(_,prefix,_,_)).
   infix(op(_,infix,_,_)).
   postfix(op(_,postfix,_,_)).


%  Comparing operator precedences.  oper_prec(LR1,LR2,HL,Op1,Op2) is true if 
%  the LR2 (i.e. left/right) precedence of the operator Op2 is HL (i.e. 
%  higher/lower) than the LR1 precedence of Op1.

% Op1 must be postfix if this question is of interest
   oper_prec(left,left,higher,Op1,Op2) :-
       Op1 = op(_,postfix,P1,M1), Op2 = op(_,Fix2,P2,M2),
       (P1 < P2; P1 = P2, (M2 = yf ; M2 = yfx ; M2 = yfy)), !.

% Op2 must be prefix if this question is of interest
   oper_prec(right,right,lower,Op1,Op2) :-
       Op1 = op(_,Fix1,P1,M1), Op2 = op(_,prefix,P2,M2),
       (P2 < P1;  P1 = P2, (M1 = fy ; M1 = xfy ; M1 = yfy)), !.

   oper_prec(right,left,lower,Op1,Op2) :-
       Op1 = op(_,Fix1,P1,M1), Op2 = op(_,Fix2,P2,M2),
       (P2 < P1 ; P1 = P2 , (M1 = fy ; M1 = xfy ; M1 = yfy)), !.

   oper_prec(right,left,higher,Op1,Op2) :-
       Op1 = op(_,Fix1,P1,M1), Op2 = op(_,Fix2,P2,M2),
       (P1 < P2 ; 
        P1 = P2, (M1 = fx ; M1 = xfx ; M1 = yfx),
                 (M2 = yf ; M2 = yfx ; M2 = yfy)), !.





%      ADDING A TERM (ACTUALLY, A <TERM,TYPE> PAIR) TO THE TERM STACK

% If there is an infix or prefix operator waiting for a term then put the 
% term into the stack and change the status of the operator
stack_term(Mod,Tok_Ty,TS,[[FX,Op]|OS],[Tok_Ty|TS],[Op|OS],CL,CL,VL,VL,W,false)
									 :- !.
% if this is the first term to go into the term stack then simply put it there
stack_term(Mod,Tok_Ty,[],OS,[Tok_Ty],OS,CL,CL,VL,VL,W,false) :- !.

% otherwise an application must be inserted
stack_term(Mod,Tok_Ty,TS,OS,[Tok_Ty|TTS], [AppOp|TOS],CL,NCL,VL,NVL,W,Err) :-
	!,
	apply_op(AppOp),
	stack_op(Mod,AppOp,TS,OS,TTS,[[in,AppOp]|TOS],CL,NCL,VL,NVL,W,Err).





%                 COLLAPSING THE STACKS TO FORM A TERM

%  If the stacks are empty or if there is an operator that expects an argument,
%  signal a syntax error. Else invoke make_term1 to form a <term,type> pair.

  make_term(Mod,[],[],_,_,_,_,_,Line,true) :-
					syntax_error(term,none,Line), !.
  make_term(Mod,TS,[[FX,Op]|OS],_,_,_,_,_,W,true) :- 
					syntax_error(term,oper_arg,Op,W), !.
  make_term(Mod,TS,OS,Term_Ty,Cl,NCl,Vl,NVl,W,Err) :- 
			!, make_term1(Mod,TS,OS,Term_Ty,Cl,NCl,Vl,NVl,W,Err).


% If operator stack is empty, term stack must contain the desired pair
  make_term1(Mod,[Term_Ty],[],Term_Ty,Cl,Cl,Vl,Vl,W,false) :- !.

% If there is an operator in the OS, form a term with it and repeat the process
  make_term1(Mod,TS,[Op|ROS],Term_Ty,Cl,NCl,Vl,NVl,W,Err) :-
                form_term(Mod,Op,TS,TTS,Cl,TCl,Vl,TVl,W,Termerr), !,
                (Termerr = true, Err =true ;
                 make_term1(Mod,TTS,ROS,Term_Ty,TCl,NCl,TVl,NVl,W,Err)), !.





%  Using the operator from the top of the OS and term(s) from the top of the
%  TS to form a term and shrinking the TS appropriately. Some bookkeeping on 
%  constants and variables must be done at this stage.


% If operator is '^' then form a application out of the top of stack terms

  form_term(Mod,Op,[A,B|Temp_TS],[Appl_term|Temp_TS],Cl,NCl,Vl,NVl,W,Err) :- 
	apply_op(Op), 
	form_appl(Mod,A,B,Appl_term,Cl,NCl,Vl,NVl,W,Err), 
	!.


% If operator is '\', form the abstraction and lp_remove the binder variable from
% the var list since its scope is over. Also rename the binder variable if 
% necessary so as to keep bound variable names distinct.

  form_term(Mod,Op,[A,B|Temp_TS],[Abst_term|Temp_TS],Cl,NCl,Vl,NVl,W,Err) :- 
	abst_op(Op), !,	B = [Binder,Ty1], 
	A = [Exp,Ty2],     % A may be atomic; check type constraints
	check_type_constraints(Mod,Exp,Cl,NCl,Vl,TVl,W,Err),
	( Err = true ;
	  lp_remove_first(Binder,TVl,NVl), 
	  (same_name_occurs(Binder,Exp),         % renaming is necessary
	      alpha_convert(Binder,Exp,NB,NE), Abst_term = [NB\NE,Ty1 ---> Ty2] ;
	   Abst_term = [Binder \ Exp, Ty1 ---> Ty2])	), 
	!.


% If operator is post- or pre-fix, form an application out of it and top of TS

  form_term(Mod,Op,[Term|Temp_TS],[Post_term|Temp_TS],Cl,NCl,Vl,NVl,W,Err) :-
	(postfix(Op) ; prefix(Op)), !,
	opname(Op,Opname), 
	form_appl(Mod,Term,[cv(Opname,Ty,c),Ty],Post_term,Cl,NCl,Vl,NVl,W,Err),
	!.


% Otherwise the operator is infix; form the appropriate application

  form_term(Mod,Op,[A,B|Temp_TS],[In_term|Temp_TS],Cl,NCl,Vl,NVl,W,Err) :- 
	opname(Op,Opname), 
	form_appl(Mod,B,[cv(Opname,Ty,c),Ty],Temp,Cl,TCl,Vl,TVl,W,Suberr), 
	(Suberr = true, Err = true ;
	 form_appl(Mod,A,Temp,In_term,TCl,NCl,TVl,NVl,W,Err)), 
	!.




%  Forming an application out of two terms. If the type constraints for the
%  application cannot be resolved with those provided through the variable
%  and constant lists and through the database assertions, an error results.

   form_appl(Mod,[Rand,Ty1],[Rator,Ty],Exp,Cl,NCl,Vl,NVl,W,Err) :-
	check_type_constraints(Mod,Rand,Cl,TCl,Vl,TVl,W,Err1), 
	( Err1 = true, Err = true ;
	  check_type_constraints(Mod,Rator,TCl,NCl,TVl,NVl,W,Err2),
	  (Err2 = true, Err = true ;
	   Ty = Ty1 ---> Ty2, Err = false, Exp = [Rator ^ Rand, Ty2] ;
	   Err = true, 
		syntax_error(term,appl,Ty,Rator,Ty1,Rand,Mod,W) ) ), 
	!.





%  These routines maintain constant and free variable lists used in performing
%  type inference and in ensuring consistent typing. Errors are pointed out
%  here if user provides types that cannot be resolved with those inferred or
%  with those provided by him/her elsewhere.

  check_type_constraints(Mod,cv(_,Ty,c),Cl,Cl,Vl,Vl,_,false) :-
			(stringtype(Ty1), Ty == Ty1 ; 
			 integertype(Ty1), Ty == int), !.

  check_type_constraints(Mod,cv(Name,Ty,v),Cl,Cl,Vl,NVl,Line,Err) :-
	((type_instance(Mod,Name,Ty1) ; lp_member(cv(Name,Ty1,v),Vl)), !,
		(Ty = Ty1, Err = false, NVl = Vl ;
		 Err = true, 
		    syntax_error(term,type,Name,Ty,Ty1,Line)) ;
	 Err = false, NVl = [cv(Name,Ty,v)|Vl]  ), 
	!.

  check_type_constraints(Mod,cv(Name,Ty,c),Cl,NCl,Vl,Vl,Line,Err) :-
	((type_instance(Mod,Name,Ty1) ; lp_member(cv(Name,Ty1,c),Cl)), !,
		(Ty = Ty1, !, Err = false, NCl = Cl ;
		 Err = true, 
		    syntax_error(term,type,Name,Ty,Ty1,Line)) ;
	 Err = false, NCl = [cv(Name,Ty,c)|Cl]  ), 
	!.

  check_type_constraints(Mod,_,Cl,Cl,Vl,Vl,_,false). % The non-atomic case

% Before looking carefully through the mlink graph for a type
% declaration, check first it some declaration exists anywhere.
  type_instance(Module,Tok,Type) :-
        (type(_,Tok,_),!, type_find(Module,Tok,Type); fail).

  type_find(Module,Tok,Type) :- type(Module,Tok,Type), !.
  type_find(Module,Tok,Type) :-
	!, mlink(Module,Mod), type_find(Mod,Tok,Type), !.




%              COLLAPSING THE STACKS TO FORM A LIST

% If the top of OS is an operator expecting an argument, signal an error
 make_list(Mod,_,[[Fx,Op]|_],_,_,_,_,_,Line,true) :-
		opname(Op,Tok), syntax_error(term,list,oper_arg,Tok,Line), !.

% If the stacks are empty, then the list is the empty one
 make_list(Mod,[],[],[cv(Nil,Ty,c),Ty],Cl,Cl,Vl,Vl,_,false) :-
					list_nil(cv(Nil,Ty,c)), !.

% Otherwise expose the topmost list operator and then invoke make_list1
 make_list(Mod,TS,OS,List_Ty,Cl,NCl,Vl,NVl,Line,Err) :-
	expose_top(Mod,TS,TTS,OS,TOS,Cl,TCl,Vl,TVl,Line,Err1),
	(Err1 = true, Err = true ;
	 make_list1(Mod,TTS,TOS,List_Ty,TCl,NCl,TVl,NVl,Line,Err)), !.


% If OS is empty or topmost list operator is ',', a nil must be added to TS.
 expose_top(Mod,TS,[[Nil,Ty]|TS],OS,[CommaOp|OS],Cl,Cl,Vl,Vl,Line,false) :-
	(OS = [] ; OS = [Op|_], opname(Op,',')), !,
	list_nil(Nil), Nil = cv(_,Ty,_),
	oper_instance(Mod,Fx,P,',',M), CommaOp = op(',',Fx,P,M),
	!.

% When the top of the OS is '|', it must be replaced with ',' .
 expose_top(Mod,TS,TS,[Op|OS],[CommaOp|OS],Cl,Cl,Vl,Vl,Line,false) :-
	opname(Op,'|'), !,
	oper_instance(Mod,Fx,P,',',M), CommaOp = op(',',Fx,P,M).

% Otherwise form the top of stack term and repeat the process.
 expose_top(Mod,TS,NTS,OS,NOS,Cl,NCl,Vl,NVl,Line,Err) :-
	OS = [Op|ROS],
	form_term(Mod,Op,TS,TTS,Cl,TCl,Vl,TVl,Line,TermErr),
	(TermErr = true, Err = true ;
	 expose_top(Mod,TTS,NTS,ROS,NOS,TCl,NCl,TVl,NVl,Line,Err)),
	!.



% If the OS is empty and the TS contains only one element, then it is the list
 make_list1(Mod,[List_Ty],[],List_Ty,Cl,Cl,Vl,Vl,_,false) :- !.


% If the top of OS operator is ',', form a cons out of the top two terms in TS.
% If it is '|', then signal error. Otherwise form the 'top' term and repeat.
 make_list1(Mod,TS,[Op|OS],List,Cl,NCl,Vl,NVl,Line,Err) :- 
	opname(Op,OpName), !,
	(OpName = ',',
	    TS = [Tail,Head|RTS], 
	    list_cons(Cons), Cons = cv(_,Ty,_), Cons_Ty = [Cons,Ty],
	    form_appl(Mod,Head,Cons_Ty,TLst,Cl,TCl,Vl,TVl,Line,Err1),
		(Err1 = true, Err = true ;
		 form_appl(Mod,Tail,TLst,Lst,TCl,TTCl,TVl,TTVl,Line,Err2),
		 (Err2 = true, Err = true ;
		  make_list1(Mod,[Lst|RTS],OS,List,TTCl,NCl,TTVl,NVl,Line,Err))
		) ;
	 OpName = '|', 
		Err = true, syntax_error(term,list,oper,OpName,Line) ;
	 form_term(Mod,Op,TS,TTS,Cl,TCl,Vl,TVl,Line,TermErr),
		(TermErr = true, Err = true ;
		 make_list1(Mod,TTS,OS,List,TCl,NCl,TVl,NVl,Line,Err) ) ),
	!.



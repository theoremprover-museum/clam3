% This file contains some initialisations that are necessary for the lambda
%  prolog system to run.  

  :- dynamic import/2, mlink/2, path_name/1.

% These define operators that are used in Prolog to represent abstraction,
% application and the function type constructor
  :- op(164,xfy,\).    
  :- op(165,yfx,^).    
  :- op(150,xfy,--->).   

% Predicates for finding the names of some of the types. These are defined here
% just in case better names are desired. Only int.pro uses the names directly.
  integertype(int).
  stringtype(string). 

% Names of some lambda Prolog constants. Used to make rest of the code as 
% independent of specific names as possible.
  list_cons(cv(internalcons,A ---> (list ^ A) ---> (list ^ A),c)).
  list_nil(cv(internalnil,(list ^ A),c)).
  turnstile(cv((':-'), o ---> o ---> o,c)).

% adding access to system modules from main.

  import(main,[sys_defs]).
  mlink(main,sys_defs).


  system_module(X) :- lp_member(X,[sys_defs,fp_sys,lp_sys]).

  get_imports(Source, Imports) :- 
  	(import(Source,Imports) ; Imports = []), !.


% System modules reside in this directory. Before saving the system,
% the first path should be deleted using lp_remove_path.

     path_name('../sysmods/').
     path_name('./').



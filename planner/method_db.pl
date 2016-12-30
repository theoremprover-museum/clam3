/*
 * This file contains the code to update and access the method database.
 * Methods used to be stored as method/6 clauses in the asserted Prolog
 * database, but this meant that the only way of changing the method
 * database was to edit and reconsult the single (huge) file containing
 * the methods.
 * 
 * To provide a more flexible mechanism for updating the method
 * database, the code in this file stores methods in the recorded
 * database, and provides predicates for accessing and updating this
 * database.
 * 
 * Currently, the (sub)method databases are stored as a list under a
 * single the keys 'method' or 'submethod'
 * in the recorded database. Thus, accessing (sub)methods means ploughing
 * through this list. This is not the most efficient representation, and
 * should be changed sometimes, but it is the easiest one to write at
 * the moment. More efficient representations in the future are
 * - Storing methods as separate items in the recorded database.
 *   Accessing methods would then mean ploughing through all records
 *   indexed under "method" which is faster than ploughing through a
 *   list (or is it?).
 * - Storing methods as separate items in the asserted database. The
 *   major advantage is that we can use the Prolog indexing to
 *   efficiently find methods (however: how often do we look for methods
 *   with a given name...?) (On the other hand, maybe we can index on
 *   other slots of the methods (such as the postconditions, which
 *   are often given as either [] or [_|_])). This efficiency advantage
 *   of good indexing is off-set by the fact that the assert database is
 *   a pain to handle, plus the fact that NIP doesn't do any garbage
 *   collection on the assert database (whereas it does on the record
 *   database). On the other hand, Quintus 2.4.2 claims that asserting
 *   is now faster than recording. On the first hand however, maybe the
 *   record-database is the (ideologically sound place for the
 *   method-structures). 
 *
 * We are using separate databases for methods and submethods, since we
 * often know wether we are looking for a method or a submethod, thus
 * reducing the search time by keeping two small databases, rather than
 * one large one.
 * 
 * The fact that we are no longer using straight asserts to read methods
 * in from a file into the database also means that we can afford to
 * have different internal and external representations for methods.
 * Previously, both internal and external representations were
 * (sub)method/6 clauses, with the exception of iterators, for which the
 * external representation was
 * 
 *      iterate_(sub)methods(_,Method)
 * 
 * and the internal representation was
 * 
 *      method(iterator(Method,_),_,_,_,_,_)
 * 
 * In this new version, we will use the following external representations:
 * 
 * [1] method(MethodName(...),Input,PreConds,PostConds,Output,Tactic):
 *      an explicitly specified method. 
 * [2] iterator(method, MethodName, methods, MethodList):
 *      a method constructed by iterating other methods.
 * [3] iterator(method, MethodName, submethods, SubMethodList):
 *      a method constructed by iterating other submethods.
 * [4] submethod(SubMethodName(...),Input,PreConds,PostConds,Output,Tactic):
 *      an explicitly specified submethod.
 * [5] iterator(submethod, SubMethodName, methods, MethodList):
 *      a submethod constructed by iterating other methods.
 * [6] iterator(submethod, SubMethodName, submethods, SubMethodList):
 *      a submethod constructed by iterating other submethods.
 *
 * The corresponding internal representations are:
 * 
 * [1] method(MethodName(...),Input,Pre,Post,Output,Tactic)
 * [2] method(MethodName([..MethodCalls..]),In,Pre,Post,Out,Tactic)
 * [3] method(MethodName([..SubMethodCalls..]),In,Pre,Post,Out,Tactic)
 * [4] submethod(SubMethodName(...),Input,Pre,Post,Output,Tactic)
 * [5] submethod(SubMethodName([...MethodCalls...]),In,Pre,Post,Out,Tactic)
 * [6] submethod(SubMethodName([...SubMethodCalls...]),In,Pre,Post,Out,Tactic)
 *
 * Notice that [1]=[2]=[3] and [4]=[5]=[6], so that external
 * method_iterator- and 
 * submethod_iterator clauses get mapped into the same internal
 * representation as normal methods and submethods, thus giving only 2
 * different internal representations 
 * for 6 external representations. (The difference between [2] and [3]
 * (and similarly between [5] and [6]) is expressed in the use of
 * applicable/4 or applicable_submethod/4 in the preconditions of the
 * method).
 *
 * Notice also that the above representations force iterated
 * (sub)methods to be of arity 1, with the single argument representing 
 * the sequence of calls to the iterated methods.
 *
 * This file is organised in the following sections:
 * [1] The code for loading methods from an external file into the
 *     internal databases
 * [2] Other predicates for manipulating and inspecting the databases
 * [3] The predicates which define the internal and external
 *     representations for methods, plus conversions between them.
 * [4] Initialisation of the databases at load/compile time.
 */

/*************************************************************************
 * Section [1] of this file: The code for loading methods from an
 * external file into the internal databases.
 * Main entry points are load_method/[1;2;3] and load_submethod/[1;2;3].
 * Real work is done by load_mthd/[2;3;4] (and mainly load_mthd/4).
 * Supporting predicates are
 * - read_ext_mthds/4 (for reading from file)
 * - delete_existing_method/4 (for removing old methods from database)
 * - insert_methods/5 (for inserting new methods into databse)
 */

        % load_method(+Functor/Arity, +Where, +Dir) loads the method
        % specified by Functor/Arity from the correct file in directory
        % Dir into the method database  at position Where.
        % Furthermore, all methods needed by the Functor/Arity method
        % (as specified by the needs/2 database), and not currently
        % loaded, will be loaded as well.
        % 
        % The first argument can also be a list of Functor/Arity
        % specifications, in which case all of these will be loaded from
        % their files in Dir.
        % 
        % load_submethod(+Functor/Arity, +Where, +Dir) is similar,
        % except for submethods.
        % 
        % A method is specified as F/A. All expressions in File
        % concerning the method are read. These expressions (the
        % possible external representations of the method F/A) can be any
        % of the following (where Method is a functor F of arity A):
        % 
        % - method(Method,In,Pre,Out,Pos,Tactic)
        % - iterator(method, MethodName, methods, MethodList):
        % - iterator(method, MethodName, submethods, SubMethodList)
        % - submethod(SubMethod,In,Pre,Out,Pos,Tactic)
        % - iterator(submethod, SubMethodName, methods, MethodList)
        % - iterator(submethod, SubMethodName, submethods, SubMethodList)
        % 
        % All expressions in File concerning the method F/A will be
        % read. The order in which they occur in File will be the order
        % at which they will be inserted in the database.
        % 
        % The specification of the position Where can be one of:
        % 
        % - first: put Method as the first item in the database
        % - last:  put Method as the last item in the database
        % - before(M): put Method in the database just before method M.
        % - after(M):  put Method in the database just after method M.
        % 
        % As a result of loading Method, any existing methods with names
        % F/A will be deleted. In other words, load_method behaves like
        % reconsult, not like consult.
        % 
        % load_(sub)method/[1;2] provide defaults for Where and Dir.
        % The default value for Where is the current position of Method
        % if Method already exists in the database, or "last" otherwise.
        % The default value for Dir is LIBDIR as defined by the
        % lib_dir/1 predicate.
        % 
        % Because of the overloading of the second argument of
        % load_(sub)method/2 (either Where or Dir), directories should
        % not be named 'first' or 'last'...
        % 
        % First we map both load_method/[1;2;3] and
        % load_submethod/[1,2,3] into load_mthd/[2;3;4] which has
        % as an additional first argument the type of the method to be
        % loaded (method or submethod), so that both can be uniformly
        % treated by the same code.
        % Thus, in the code for load_mthd/[2;3;4], wherever it says
        % "Method", you should read "Method or SubMethod".
load_method(M/A):-                load_mthd(method,M/A).
load_method(M/A,WhereorDir) :-    load_mthd(method,M/A,WhereorDir).
load_method(M/A,Where,Dir) :-     load_mthd(method,M/A,Where,Dir).
load_submethod(M/A):-             load_mthd(submethod,M/A).
load_submethod(M/A,WhereorDir) :- load_mthd(submethod,M/A,WhereorDir).
load_submethod(M/A,Where,Dir) :-  load_mthd(submethod,M/A,Where,Dir).
load_hint(M/A):-                  load_mthd(hint,M/A).
load_hint(M/A,WhereorDir) :-      load_mthd(hint,M/A,WhereorDir).
load_hint(M/A,Where,Dir) :-       load_mthd(hint,M/A,Where,Dir).

        % The first 3 clauses of load_mthd are just for providing
        % default values: 
        % Determine default value for Dir:
load_mthd(Type,M/A) :-
    lib_dir(LibDir),
    load_mthd(Type,M/A, LibDir).
        % Iterative version:
load_mthd(_,[]).
load_mthd(Ty,[H|T]) :- load_mthd(Ty,H), load_mthd(Ty,T).
        % We have to disambiguate the overloaded second argument of
        % load_mthd/3. If it is a position specifier, we provide
        % the default value for Dir, otherwise it is taken to be a
        % filename, and we provide the default value for Where:
load_mthd(Type,M/A, Where) :-
    lib_dir(LibDir),
    member(Where, [first,last,before(_),after(_)]),!,
    load_mthd(Type,M/A, Where, LibDir).
        % Determine default value for Where:
        % If Method already occurs in the database, pass on its position
        % as an integer (counting from 0), otherwise default value is "last".
        % 
        % To find out if Method already occurs in the database, we have
        % to plough through the database and see if any of the internal
        % representations of the Method occurs. Remember that Method is
        % specified as F/A, and that its internal representations can be
        % any of:
        % 
        % - method(Method,_,_,_,_,_)
        % - submethod(Method,_,_,_,_,_)
        % (where Method is functor F or arity A).
        % 
load_mthd(Type, M/A, Dir) :-
    recorded( Type, MethodList, _ ),
    (nth0(Where,MethodList,M/A)
     orelse
     Where=last
    ),
    load_mthd(Type,M/A,Where, Dir).
        % Iterative version:
load_mthd(_,[],_).
load_mthd(Ty,[H|T],WD) :- load_mthd(Ty,H,WD), load_mthd(Ty,T,WD).
        % (At this point we have:
        %   Type = {method,submethod},
        %   Method = M/A,
        %   Where = {N>=0, first, last, before(_), after(_)}
        %   Dir = Atompathname
        % )
        % load_mthd/4 does the real work:
        % [1] Check consistency of Where-specification;
        % [2] Check consistency of File-specification;
        % [2.5] Load all methods needed by Method;
        % [3] Read all the external representations for Method from  File;
        % [4] Transform the ext. representations into int. representations;
        % [5] Delete existing versions of Method (if any);
        % [6] Insert new internal representations into database;
        % [7] Install new database.
load_mthd(Type,M/A, Where, Dir) :-
 % [1] Check consistency of Where-specification:
    (  integer(Where),Where>=0
     ; member(Where, [first,last])
     ; member(Where, [before(M1),after(M1)]),
       (list_methods(Type,Mthds), member(M1,Mthds)
        ; writef('CLaM ERROR: %t %t does not occur in database\n',[Type,M1]),
        !,fail
       )
    ),!,
 % [2] Check consistency of File-specification
    (Type=method, Suffix=mthd ; 
     Type=submethod, Suffix=smthd ;
     Type=hint, Suffix=hint),
    lib_fname( Dir, M, Suffix, File ),
    (file_exists(File)
     orelse
     (writef('CLaM ERROR: cannot find file %t\n',[File]),!,fail)
    ),!,
    (Type=method,PType=mthd ;
     Type=submethod,PType=smthd ;
     Type=hint,PType=hint),
 % [2.5] Load all methods needed by Method:
    NType =.. [PType,M/A],
    needs(NType,Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Dir)),!,
 % [3] Read all the external representations for Method from  File;
    writef('loading %t(%t) %f', [PType,M/A]),
    read_ext_mthds(Type,M/A,File,Externals),
 % [4] Transform the ext. representations into int. representations;
    map_list(Externals, Ext:=>Int, ext2int(Ext,Int), Internals),
    recorded( Type, MethodList, _ ),
 % [5] Delete existing versions of Method (if any);
    ( del(MethodList, M/A, CleanList) ; MethodList = CleanList ),
 % [6] Insert new internal representations into database.
    insert_methods(Where, Type, M/A, CleanList, NewList),
    Tag =.. [Type, A, Internals],
    uniq_recorda( M, Tag, _ ),
 % [7] Install new database.
    uniq_recorda( Type, NewList, _ ),
    writef(' done\n'),
    !.

        % Iterative version:
load_mthd(_,[],_,_).
load_mthd(Ty,[H|T],W,F) :- load_mthd(Ty,H,W,F), load_mthd(Ty,T,W,F).

        % read_ext_mthds(+Type, +M/A, +File, ?Externals) reads from
        % File all external representations for Method (or SubMethod,
        % depending on Type).
        %
        % First we try to open File, or if that does not exist File.mthd,
        % or produce an error and fail if that doesn't exist either,
        % then open File, call the read-loop to do the real work, and
        % close File. The read-loop will never fail, so File will always
        % be closed. 
read_ext_mthds(Type, M/A, File, Externals) :-
    (file_exists(File)
     orelse
     (writef('\nCLaM INTERNAL ERROR[3]: load_%t cannot find file %t \n',
             [Type,File]), !,fail)
    ),
    % seeing(OldFile),
    see(File),
    do_read_ext_mthds(Type, M/A, Externals),
    seen,
    % see(OldFile),
    (Externals\==[]
     orelse
     (writef('\nCLaM ERROR: %t %t not found in file %t\n',[Type,M/A,File]),
      !,fail)
    ).
        % Actual read-loop. We need the terrible if-then-else code
        % because we can only make one call to read/1...
do_read_ext_mthds(Type, M/A, Externals) :-
    read(Exp),
    ( (Exp == end_of_file)                 % if eof
     -> Externals=[]                     %  then terminate
     ; (mthd_ext(M/A,Type,Exp)           %  else if reading required method
        -> (Externals=[Exp|Rest],        %        then collect method
            writef('.%f'))               %             and report progress
        ;  Externals=Rest                %        else dont collect method
       ),                                %       fi
       do_read_ext_mthds(Type, M/A, Rest)%      continue reading
    ).                                  % fi



        % insert_methods(+Where, +Type, +NewMethods, +OldList, ?NewList)
        % Inserts the methods specified in NewMethods (a list of
        % internal method representations) in OldList at position Where,
        % giving NewList. Works for both methods and submethods,
        % depending on Type. OldList is assumed to be already :"clean",
        % that is: not containing any old code for any of the
        % NewMethods.
        % 
        % First 2 clauses deal with Where={first,last}: we can just
        % append or prepend.
insert_methods(first, _Type, NewMethod, OldList, NewList) :- !,
    [NewMethod|OldList] = NewList.
insert_methods(last, _Type, NewMethod, OldList, NewList) :- !,
    append(OldList, [NewMethod], NewList).
        % Next 2 clauses deal with Where={before(_),after(_)}. We transform
        % the position specified by Where into a number, and let the 5th
        % clause do the work.
insert_methods(before(M), Type, Method, OldList, NewList) :- !,
    list_methods(Type,Ms),
    (nth0(N,Ms,M)
     orelse
     (writef('\nCLaM INTERNAL ERROR[1]: %t %t does not occur in database\n',
            [Type,M]), !,fail)
    ),
    insert_methods(N, Type, Method, OldList, NewList).
insert_methods(after(M), Type, Method, OldList, NewList) :- !,
    list_methods(Type,Ms),
    (% Find the position of the last occurence ofMInt in OldList:
     (findall(N1,nth0(N1,Ms,M),N1s),last(N1,N1s))
     orelse
     (writef('\nCLaM INTERNAL ERROR[2]: %t %t does not occur in database\n',
             [Type,M]), !,fail)
    ),
    N is N1+1,
    insert_methods(N, Type, Method, OldList, NewList).
        % 5th clause deals with Where=N, N>0. Split OldList up into
        % 1,...,N and N+1,...,end and use appends to glue the new
        % methods in the middle. 
insert_methods(N, _Type, NewMethod, OldList, NewList) :-
    integer(N),N>=0,!,
    same_length(First,_,N),
    append(First, Last, OldList),
    append(First, [NewMethod], NewAndFirst),
    append(NewAndFirst, Last, NewList).
        % last clause traps illegal position specifiers. 
insert_methods(W, T, _,_,_) :-
    writef('CLaM ERROR: Illegal specification %t of position in %t database\n',
           [W,T]),
    writef('should be one of: first, last, before(_), after(_), integer>0.\n'),
    !,fail.


/*************************************************************************
 * Section [2] of this file: The code for other predicates for
 * manipulating and inspecting the databases.
 * Main entry points are
 * - method/2 for accessing the recorded list of (sub)methods names/arities
 * - method/6 and submethod/6 for accessing the databases
 * - delete_method/1 and delete_submethod/1 for removing specific methods
 * - delete_methods/0 and delete_submethods/0 for removing all methods.
 * - list_methods/[0;1] and list_submethods/[0;1] for listing the databases
 */

        % method(+Type, ?Name/?Arity)
        % is the predicate to look up a (sub)method's name and aity.
method(Type, Name/Arity):-
    recorded(Type, MethodList, _),
    member(Name/Arity, MethodList).

        % (sub)method(?Method,?Input,?PreConds,?PostConds,?Output,?Tactic)
        % is the predicate to look up (sub)methods in the database. The
        % real work is done by mthd/7, which treats methods and
        % submethods uniformly. 
method(Method,Input,PreConds,PostConds,Output,Tactic) :-
    mthd(method,Method,Input,PreConds,PostConds,Output,Tactic).
submethod(Method,Input,PreConds,PostConds,Output,Tactic) :-
    mthd(submethod,Method,Input,PreConds,PostConds,Output,Tactic).
hint(Method,Input,PreConds,PostConds,Output,Tactic) :-
    mthd(hint,Method,Input,PreConds,PostConds,Output,Tactic).
        % Iterate through the appropriate database and match the
        % internal representation agains the specified method-slots.
mthd(Type,Method,Input,PreConds,PostConds,Output,Tactic) :-
    \+ var(Method),!,
    functor(Method,M,A),
    Tag =.. [Type,A,Internals],
    recorded( M, Tag,_ ),
    member( Internal, Internals ),
    Internal =.. [Type, Method,Input,PreConds,PostConds,Output,Tactic].
mthd(Type,Method,Input,PreConds,PostConds,Output,Tactic) :-
    recorded( Type, MethodList, _ ),
    member(M/A,MethodList),
    Tag =.. [Type,A,Internals],
    recorded( M, Tag,_ ),
    member( Internal, Internals ),
    Internal =.. [Type, Method,Input,PreConds,PostConds,Output,Tactic].

        % delete_method(+Method) and
        % delete_submethod(+Method) delete the (Sub)Method specified by
        % Method (of the form F/A) from the appropriate database.
        % We also provide iteration if Method is a list of (sub)methods
        % instead of a single method.
delete_method(M/A) :-    delete_method(method, M/A).
delete_method([]).
delete_method([H|T]) :- delete_method(H),delete_method(T).
delete_submethod(M/A) :- delete_method(submethod, M/A).
delete_submethod([]).
delete_submethod([H|T]) :- delete_submethod(H),delete_submethod(T).
delete_hint(M/A) :-    delete_method(hint, M/A).
delete_hint([]).
delete_hint([H|T]) :- delete_hint(H),delete_hint(T).

delete_method(Type, M/A) :-
    recorded( Type, OldList, _ ),
    ( del(OldList, M/A, NewList) ;
      writef('CLaM ERROR: %t %t does not occur in current database\n',
               [Type,M/A]),
        !,fail
    ),
    uniq_recorda(Type, NewList, _ ),
    Tag =.. [Type,A,_],
    recorded( M, Tag, Ref ),
    erase( Ref ).
delete_method(_,[]).
delete_method(Ty,[H|T]) :- delete_method(Ty,H), delete_method(Ty,T).

        % delete_methods and delete_submethods erase the whole of the
        % appropriate database.
        % Work done uniformly for both methods and submethods by
        % delete_methods/1 which distinguishes two cases: second clause
        % if no previous database exists (useful for initialisation),
        % first clause when database does exist.
delete_methods :- delete_mthds(method).
delete_submethods :- delete_mthds(submethod).
delete_mthds(Type) :-
    recorded( Type, Old, _ ),
    ( member( M/A, Old ),
      Tag =.. [ Type, A, _ ],
      recorded( M, Tag, Ref ),
      erase( Ref ),
      fail ;
      uniq_recorda( Type, [], _ )
    ).

        % list_methods/0 and list_submethods/0 list the order of the
        % relevant databases.
        % list_methods/1 and list_submethods/1 return the contents of
        % the current database as a list of F/A specifications (in other
        % words, this is the list as printed by list_(sub)methods/0).
list_methods :- list_methods(L), nl, prlist(L).
list_methods(L) :- recorded(method,L,_).
list_submethods :- list_submethods(L), nl, prlist(L).
list_submethods(L) :- recorded(submethod,L,_).
list_hints :- list_hints(L), nl, prlist(L).
list_hints(L) :- recorded(hint,L,_).
list_methods(Type, L) :- recorded(Type, L , _ ).



/*************************************************************************
 * Section [3] of this file: The predicates which define the internal
 * and external representations for methods, plus conversions between
 * them.
 * Main entry points are
 * - mthd_ext/3 for external representations of methods,
 * - mthd_int/3 for internal representations of methods,
 * - ext2int/2 for translating external to internal representations.
 */

        % mthd_ext(F/A, Type, External) and
        % mthd_int(F/A, Type, Internal) map method-specifications of the
        % form F/A into the correct external and internal representations.
        % 
        % The method-argument to the predicates load_method/[1;2;3] and
        % delete_method/1 is specified as F/A. For such a method a
        % number of method-specifying expressions can occur in a file.
        % These external representations of a method are:
        % 
        % - method(Method,In,Pre,Out,Pos,Tactic)
        % - iterator(method, MethodName, methods, MethodList):
        % - iterator(method, MethodName, submethods, SubMethodList)
        % - submethod(SubMethod,In,Pre,Out,Pos,Tactic)
        % - iterator(submethod, SubMethodName, methods, MethodList)
        % - iterator(submethod, SubMethodName, submethods, SubMethodList)
        % 
        % (where Method is a functor F of arity A).
        %
        % The representation forces iterated (sub)methods to be of arity
        % 1, with the single argument representing the sequence of calls
        % to the iterated methods. 
mthd_ext(F/A,Type,Term) :-
    Term =.. [Type,M,_,_,_,_,_],
    functor(M,F,A).
mthd_ext(F/1,Type,iterator(Type,F,_,_)) :-
    (Type=method ; Type=submethod).
        %
        % Each of these external method representations corresponds to
        % an internal representation of the method in the database. These
        % internal method representations are:
        % 
        % - method(Method,In,Pre,Out,Pos,Tactic)
        % - submethod(SubMethod,In,Pre,Out,Pos,Tactic)
        % 
mthd_int(F/A,method,method(M,_,_,_,_,_)) :- functor(M,F,A).
mthd_int(F/A,submethod,submethod(SubM,_,_,_,_,_)) :- functor(SubM,F,A).
mthd_int(F/A,hint,hint(M,_,_,_,_,_)) :- functor(M,F,A).

        % ext2int(+External,?Internal) maps an external representation
        % of a method into the corresponding internal representation,
        % either doing it directly (for easy cases, such as explicitly
        % specified methods), or indirectly using iterate_methods/3 (for
        % iterating methods).
ext2int(method(M,I,Pr,Po,O,T),
        method(M,I,Pr,Po,O,T)).
ext2int(iterator(method,M,Types,Ms),
        method(M1,I,Pr,Po,O,T)) :-
    iterate_methods(M,Ms,Types,method(M1,I,Pr,Po,O,T)).
ext2int(submethod(M,I,Pr,Po,O,T),
        submethod(M,I,Pr,Po,O,T)).
ext2int(iterator(submethod,SM,Types,Ms),
        submethod(SM1,I,Pr,Po,O,T)) :-
    iterate_methods(SM,Ms,Types,submethod(SM1,I,Pr,Po,O,T)).
ext2int(hint(M,I,Pr,Po,O,T),
        hint(M,I,Pr,Po,O,T)).
ext2int(iterator(hint,M,Types,Ms),
        hint(M1,I,Pr,Po,O,T)) :-
    iterate_methods(M,Ms,Types,hint(M1,I,Pr,Po,O,T)).

/*************************************************************************
 * Section [4] of this file: Initialisation of the databases at
 * load/compile time.
 *
 */

        % Deleting a non-existent database results in the installation
        % of an empty database:
:- uniq_recorda(method,[],_).
:- uniq_recorda(submethod,[],_).
:- uniq_recorda(hint,[],_).

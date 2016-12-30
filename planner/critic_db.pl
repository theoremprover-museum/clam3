/*
 * This file contains the code to update and access the critic database.
 * Like the critics database the code in this file stores critics in the 
 * recorded database, and provides predicates for accessing and updating 
 * this database.
 * 
 * Currently, the critic database is stored as a list under the key 'critic'
 * in the recorded database. Thus, accessing critics means ploughing
 * through this list. This is not the most efficient representation, and
 * should be changed sometimes, but it is the easiest one to write at
 * the moment. For more efficient representations see Frank's comments
 * in critic_db.pl.
 * 
 * Representation of critics:
 * 
 *     critic(CriticName(...),Input,PreConds,Effects,Output):
 *     an explicitly specified critic. 
 *
 * This file is organised in the following sections:
 * [1] The code for loading critics from an external file into the
 *     internal databases
 * [2] Other predicates for manipulating and inspecting the databases
 * [3] Initialisation of the databases at load/compile time.
 */

/*************************************************************************
 * Section [1] of this file: The code for loading critics from an
 * external file into the internal databases.
 * Main entry points are load_critic/[1;2;3]. Real work is done by 
 * load_critic/[2;3;4] (and mainly load_critic/4).
 * Supporting predicates are
 * - read_ext_crtcs/4 (for reading from file)
 * - delete_existing_critic/4 (for removing old critics from database)
 * - insert_critics/5 (for inserting new critics into databse)
 */

        % load_critic(+Functor/Arity, +Where, +Dir) loads the critic
        % specified by Functor/Arity from the correct file in directory
        % Dir into the critic database  at position Where.
        % Furthermore, all critics needed by the Functor/Arity critic
        % (as specified by the needs/2 database), and not currently
        % loaded, will be loaded as well.
        % 
        % The first argument can also be a list of Functor/Arity
        % specifications, in which case all of these will be loaded from
        % their files in Dir.
        % 
        % A critic is specified as F/A. All expressions in File
        % concerning the critic are read. These expressions (the
        % possible external representations of the critic F/A) can be any
        % of the following (where Critic is a functor F of arity A):
        % 
        % - critic(Critic,Input,Preconds,Effects,Output)
        % 
        % All expressions in File concerning the critic F/A will be
        % read. The order in which they occur in File will be the order
        % at which they will be inserted in the database.
        % 
        % The specification of the position Where can be one of:
        % 
        % - first: put Critic as the first item in the database
        % - last:  put Critic as the last item in the database
        % - before(C): put Critic in the database just before critic C.
        % - after(C):  put Critic in the database just after critic C.
        % 
        % As a result of loading Critic, any existing critics with names
        % F/A will be deleted. In other words, load_critic behaves like
        % reconsult, not like consult.
        % 
        % load_critic/[1;2] provide defaults for Where and Dir.
        % The default value for Where is the current position of Critic
        % if Critic already exists in the database, or "last" otherwise.
        % The default value for Dir is LIBDIR as defined by the
        % lib_dir/1 predicate.
        % 
        % Because of the overloading of the second argument of
        % load_critic/2 (either Where or Dir), directories should
        % not be named 'first' or 'last'...
        % 
        % First we map both load_critic/[1;2;3] and
        % load_critic/[1,2,3] into load_critic/[2;3;4] which has
        % as an additional first argument the type of the critic to be
        % loaded (critic or subcritic), so that both can be uniformly
        % treated by the same code.
        % Thus, in the code for load_critic/[2;3;4], wherever it says
        % "Critic", you should read "Critic or SubCritic".
load_critic(M/A):-                load_crtc(critic,M/A).
load_critic(M/A,WhereorDir) :-    load_crtc(critic,M/A,WhereorDir).
load_critic(M/A,Where,Dir) :-     load_crtc(critic,M/A,Where,Dir).

        % The first 3 clauses of load_critic are just for providing
        % default values: 
        % Determine default value for Dir:
load_crtc(Type,M/A) :-
    lib_dir(LibDir),
    load_crtc(Type,M/A, LibDir).
        % Iterative version:
load_crtc(_,[]).
load_crtc(Ty,[H|T]) :- load_crtc(Ty,H), load_crtc(Ty,T).
        % We have to disambiguate the overloaded second argument of
        % load_critic/3. If it is a position specifier, we provide
        % the default value for Dir, otherwise it is taken to be a
        % filename, and we provide the default value for Where:
load_crtc(Type,M/A, Where) :-
    lib_dir(LibDir),
    member(Where, [first,last,before(_),after(_)]),!,
    load_crtc(Type,M/A, Where, LibDir).
        % Determine default value for Where:
        % If Critic already occurs in the database, pass on its position
        % as an integer (counting from 0), otherwise default value is "last".
        % 
        % To find out if Critic already occurs in the database, we have
        % to plough through the database and see if any of the internal
        % representations of the Critic occurs. Remember that Critic is
        % specified as F/A, and that its internal representations can be:
        % 
        % - critic(Critic,_,_,_,_,_)
        % (where Critic is functor F or arity A).
        % 
load_crtc(Type, M/A, Dir) :-
    recorded( Type, CriticList, _ ),
    (nth0(Where,CriticList,M/A)
     orelse
     Where=last
    ),
    load_crtc(Type,M/A,Where, Dir).
        % Iterative version:
load_crtc(_,[],_).
load_crtc(Ty,[H|T],WD) :- load_crtc(Ty,H,WD), load_crtc(Ty,T,WD).
        % (At this point we have:
        %   Type = {critic,(or subcritic at some point in the future)},
        %   Critic = M/A,
        %   Where = {N>=0, first, last, before(_), after(_)}
        %   Dir = Atompathname
        % )
        % load_critic/4 does the real work:
        % [1] Check consistency of Where-specification;
        % [2] Check consistency of File-specification;
        % [2.5] Load all critics needed by Critic;
        % [3] Read Critic from  File;
        % [4] Delete existing versions of Critic (if any);
        % [5] Insert new Critic into database;
        % [6] Install new database.
load_crtc(Type,M/A, Where, Dir) :-
 % [1] Check consistency of Where-specification:
    (  integer(Where),Where>=0
     ; member(Where, [first,last])
     ; member(Where, [before(M1),after(M1)]),
       (list_critics(Type,Critics), member(M1,Critics)
        ; writef('CLaM ERROR: %t %t does not occur in database\n',[Type,M1]),
        !,fail
       )
    ),!,
 % [2] Check consistency of File-specification
    (Type=critic, Suffix=critic ; 
     Type=subcritic, Suffix=scritic ),
    lib_fname( Dir, M, Suffix, File ),
    (file_exists(File)
     orelse
     (writef('CLaM ERROR: cannot find file %t\n',[File]),!,fail)
    ),!,
    Type=critic,PType=critic,
 % [2.5] Load all critics needed by Critic:
    NType =.. [PType,M/A],
    needs(NType,Needed),
    forall {Need \ Needed}: (lib_present(Need) orelse lib_load(Need,Dir)),!,
 % [3] Read the representation for Critic from  File;
    writef('loading %t(%t) %f', [PType,M/A]),
    read_ext_crtcs(Type,M/A,File,CriticReps),
    recorded(Type, CriticList, _),
 % [4] Delete existing versions of Critic (if any);
    ( del(CriticList, M/A, CleanList) ; CriticList = CleanList ),
 % [5] Insert new internal representations into database.
    insert_critics(Where, Type, M/A, CleanList, NewList),
    Tag =.. [Type, A, CriticReps],
    uniq_recorda( M, Tag, _ ),
 % [6] Install new database.
    uniq_recorda( Type, NewList, _ ),
    writef(' done\n'),
    !.

        % Iterative version:
load_crtc(_,[],_,_).
load_crtc(Ty,[H|T],W,F) :- load_crtc(Ty,H,W,F), load_crtc(Ty,T,W,F).

        % read_ext_crtcs(+Type, +M/A, +File, ?Externals) reads from
        % File all external representations for Critic (or SubCritic,
        % depending on Type).
        %
read_ext_crtcs(Type, M/A, File, Externals) :-
    (file_exists(File)
     orelse
     (writef('\nCLaM INTERNAL ERROR[3]: load_%t cannot find file %t \n',
             [Type,File]), !,fail)
    ),
    % seeing(OldFile),
    see(File),
    do_read_ext_crtcs(Type, M/A, Externals),
    seen,
    % see(OldFile),
    (Externals\==[]
     orelse
     (writef('\nCLaM ERROR: %t %t not found in file %t\n',[Type,M/A,File]),
      !,fail)
    ).
        % Actual read-loop. We need the terrible if-then-else code
        % because we can only make one call to read/1...
do_read_ext_crtcs(Type, C/A, Externals) :-
    read(Exp),
    ( (Exp == end_of_file)               % if eof
     -> Externals=[]                     %  then terminate
     ; ((Exp =.. [Type,M,_,_,_,_],         %  else if reading required critic
         functor(M,C,A))                 % 
        -> (Externals=[Exp|Rest],        %        then collect critic
            writef('.%f'))               %             and report progress
        ;  Externals=Rest                %        else dont collect critic
       ),                                %       fi
       do_read_ext_crtcs(Type, C/A, Rest)%      continue reading
    ).                                  % fi



        % insert_critics(+Where, +Type, +NewCritics, +OldList, ?NewList)
        % Inserts the critics specified in NewCritics (a list of
        % internal critic representations) in OldList at position Where,
        % giving NewList. Works for both critics and subcritics,
        % depending on Type. OldList is assumed to be already :"clean",
        % that is: not containing any old code for any of the
        % NewCritics.
        % 
        % First 2 clauses deal with Where={first,last}: we can just
        % append or prepend.
insert_critics(first, _Type, NewCritic, OldList, NewList) :- !,
    [NewCritic|OldList] = NewList.
insert_critics(last, _Type, NewCritic, OldList, NewList) :- !,
    append(OldList, [NewCritic], NewList).
        % Next 2 clauses deal with Where={before(_),after(_)}. We transform
        % the position specified by Where into a number, and let the 5th
        % clause do the work.
insert_critics(before(M), Type, Critic, OldList, NewList) :- !,
    list_critics(Type,Ms),
    (nth0(N,Ms,M)
     orelse
     (writef('\nCLaM INTERNAL ERROR[1]: %t %t does not occur in database\n',
            [Type,M]), !,fail)
    ),
    insert_critics(N, Type, Critic, OldList, NewList).
insert_critics(after(M), Type, Critic, OldList, NewList) :- !,
    list_critics(Type,Ms),
    (% Find the position of the last occurence ofMInt in OldList:
     (findall(N1,nth0(N1,Ms,M),N1s),last(N1,N1s))
     orelse
     (writef('\nCLaM INTERNAL ERROR[2]: %t %t does not occur in database\n',
             [Type,M]), !,fail)
    ),
    N is N1+1,
    insert_critics(N, Type, Critic, OldList, NewList).
        % 5th clause deals with Where=N, N>0. Split OldList up into
        % 1,...,N and N+1,...,end and use appends to glue the new
        % critics in the middle. 
insert_critics(N, _Type, NewCritic, OldList, NewList) :-
    integer(N),N>=0,!,
    same_length(First,_,N),
    append(First, Last, OldList),
    append(First, [NewCritic], NewAndFirst),
    append(NewAndFirst, Last, NewList).
        % last clause traps illegal position specifiers. 
insert_critics(W, T, _,_,_) :-
    writef('CLaM ERROR: Illegal specification %t of position in %t database\n',
           [W,T]),
    writef('should be one of: first, last, before(_), after(_), integer>0.\n'),
    !,fail.


/*************************************************************************
 * Section [2] of this file: The code for other predicates for
 * manipulating and inspecting the databases.
 * Main entry points are
 * - critic/5 for accessing the databases.
 * - delete_critic/1 for removing specific critics.
 * - delete_critics/0 for removing all critics.
 * - list_critics/[0;1] for listing the database.
 */

        % critic(?Critic,?Input,?PreConds,?PostConds,?Output,?Tactic)
        % is the predicate to look up critics in the database. The
        % real work is done by critic/7.
critic(Critic,Input,PreConds,Effects,Output) :-
    crtc(critic,Critic,Input,PreConds,Effects,Output).
        % Iterate through the appropriate database and match the
        % internal representation agains the specified critic-slots.
crtc(Type,Critic,Input,PreConds,Effects,Output) :-
    recorded( Type, CriticList, _ ),
    member(M/A,CriticList),
    Tag =.. [Type,A,Internals],
    recorded( M, Tag,_ ),
    member( Internal, Internals ),
    Internal =.. [Type,Critic,Input,PreConds,Effects,Output].

   % delete_critic(+Critic) deletes Critic (of the form F/A) from the database.
   % An iterated version is also provided.
delete_critic(M/A) :-    delete_critic(critic, M/A).
delete_critic([]).
delete_critic([H|T]) :- delete_critic(H),delete_critic(T).

delete_critic(Type, M/A) :-
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
delete_critic(_,[]).
delete_critic(Ty,[H|T]) :- delete_critic(Ty,H), delete_critic(Ty,T).

        % delete_critics erase the whole of the database.
        % Work done uniformly for both critics by
        % delete_critics/1 which distinguishes two cases: second clause
        % if no previous database exists (useful for initialisation),
        % first clause when database does exist.
delete_critics :- delete_crtcs(critic).
delete_crtcs(Type) :-
    recorded( Type, Old, _ ),
    ( member( M/A, Old ),
      Tag =.. [ Type, A, _ ],
      recorded( M, Tag, Ref ),
      erase( Ref ),
      fail ;
      uniq_recorda( Type, [], _ )
    ).

        % list_critics/0 list the order of the
        % relevant databases.
        % list_critics/1 return the contents of
        % the current database as a list of F/A specifications (in other
        % words, this is the list as printed by list_critics/0).
list_critics :- list_critics(L), nl, prlist(L).
list_critics(L) :- recorded(critic,L,_).
list_critics(Type, L) :- recorded(Type, L , _ ).



/*************************************************************************
 * Section [3] of this file: Initialisation of the databases at
 * load/compile time.
 *
 */

        % Deleting a non-existent database results in the installation
        % of an empty database:
:- uniq_recorda(critic,[],_).






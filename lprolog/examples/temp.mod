module example.


% Kinds
kind         typ                type.
kind         term               type.

% Object-level variables
type         u                  int.
type         v                  list int.
type         w                  int.
type         x                  list int.

% Booleans
type         ybool              tp.
type         ttrue              term.
type         tfalse             term. 

% Object-level functions
type         cons               int -> list int -> list int.
type         rev                list int -> list int.
type         qrev               list int -> list int -> list int.
type         app                list int -> list int -> list int.
type         len                list int -> int.
type         perm               list int -> list int -> bool.
type         nth                int -> list int -> list int.
type         plus               int -> int -> int.
type         minus              int -> int -> int.
type         even               int -> ybool.
type         rot                int -> list int -> list int.

% Meta-level annotations
type         wf                 list int -> list int.
type         wh                 list int -> list int.

% Meta-level variables
type         X                  int.
type         Y                  int.
type         U                  int.
type         V                  list int.
type         W                  list int.
type         M                  list int -> list int.
type         N                  list int -> list int.
type         F                  list int -> int -> list int -> list int.
type         G                  list int -> int -> list int -> list int.
type         GG                 int -> int -> list int -> list int.
type         H                  int -> int.
type         I                  int -> int.
type         K                  list int -> int -> list int -> int.

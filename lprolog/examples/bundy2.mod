module bundy2.


% Kinds
kind         term               type.

% Object-level constants
type         nil                list term.

% Object-level variables
type         h                  term.
type         t                  list term.
type         l                  list term.

% Object-level functions
type         app                list term -> list term -> list term.
type         rev                list term -> list term.
type         cons               term -> list term -> list term.

% Meta-level variables
type         F                  list term -> list term -> list term.
type         U                  list term.
type         V                  list term.
type         W                  list term.


% Example

(F (app (rev t) (cons h nil)) l) = (app (app U V) W).

module bundy1.


% Kinds
kind         typ                type.
kind         term               type.
kind         real               type.

% Object-level constants
type         e                  real.

% Object-level functions
type         sin                real -> real.
type         times              real -> real -> real.
type         exp                real -> real -> real.

% Meta-level variables
type         X                  real.
type         Y                  real.
type         F                  real -> real.

% Example:

(F Y) = (times (sin X) (exp e X)). 


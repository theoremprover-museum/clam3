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

% 
% Example 1:
% 
% perm(U::V,U::W) = perm(u::v,F(rev(rev(v)),u,rev(v))) =>
% perm(u::v,u::F'(rev(rev(v)),u,rev(v)))
%
%

(perm (cons U V) (cons U W)) = (perm (cons u v) (F (rev(rev v)) u (rev v))). 

% V = v
% U = u
% W = Var2 (rev (rev v)) u (rev v)
% F = Var3 \ Var4 \ Var5 \ (cons u (Var2 Var3 Var4 Var5)) ;
% 
% 
% V = v
% U = u
% W = Var2 (rev (rev v)) u (rev v)
% F = Var6 \ Var7 \ Var8 \ (cons Var7 (Var2 Var6 Var7 Var8)) ;
%
% V = V
% U = U
% W = W
% F = F
%
%  The remaining flexible - flexible pairs:
% <Var12 (rev (rev v)) u (rev v) , F (rev (rev v)) u (rev v)>


(perm [U|V] [U|W]) = (perm [u|v] (F (rev(rev v)) u (rev v))).
% 
% V = v
% U = u
% W = Var2 (rev (rev v)) u (rev v)
% F = Var3 \ Var4 \ Var5 \ [u | Var2 Var3 Var4 Var5]
%

% V = v
% U = u
% W = Var2 (rev (rev v)) u (rev v)
% F = Var6 \ Var7 \ Var8 \ [Var7 | Var2 Var6 Var7 Var8] ;

% V = V
% U = U
% W = W
% F = F
%
%  The remaining flexible - flexible pairs:
%  <Var16 (rev (rev v)) u (rev v) , F (rev (rev v)) u (rev v)>


%  
% Example 2.
%
%

(perm (wf (cons U (wh V))) (wf (cons U (wh W)))) = 
(perm (wf (cons u (wh v))) (wf (F (wh (rev(rev v))) u (rev v)))).


% V = v
% U = u
% W = Var3 (wh (rev (rev v))) u (rev v)
% F = Var4 \ Var5 \ Var6 \ (cons u (wh (Var3 Var4 Var5 Var6))) ;
% 
% V = v
% U = u
% W = rev (rev v)
% F = Var7 \ Var8 \ Var9 \ (cons u Var7) ;
% 
% V = v
% U = u
% W = Var10 (wh (rev (rev v))) u (rev v)
% F = Var11 \ Var12 \ Var13 \ (cons Var12 (wh (Var10 Var11 Var12 Var13))) ;
%
% V = v
% U = u
% W = rev (rev v)
% F = Var14 \ Var15 \ Var16 \ (cons Var15 Var14) ;
%
% V = V
% U = U
% W = W
% F = F
%
%
%  The remaining flexible - flexible pairs:
%  <Var28 (wh (rev (rev v))) u (rev v) , F (wh (rev (rev v))) u (rev v)>

% 
% Example 3:
%
%

(perm v (F (rev (rev v)) u (rev v))) = (perm v (rev(rev v))).

%
% F = Var3 \ Var4 \ Var5 \ (rev (rev v)) ;
% 
% F = Var6 \ Var7 \ Var8 \ (rev Var8) ;
% 
% F = W1 \ W2 \ W3 \ W1 ;
%
% F = F
% 
%  The remaining flexible - flexible pairs:
% <Var21 (rev (rev v)) u (rev v) , F (rev (rev v)) u (rev v)> 

%
% Example tailrev3
%
%

(F (cons w nil) u v) = (app (rev V) (cons U nil)).

(F (cons w nil) u v) = (cons U (app V W)).

(GG w u v) = (app (rev V) (cons U nil)).

(GG w u v) = (cons U (app V W)).

(G (N x) u v) = (app (rev V) (cons U nil)).

(G (N x) u v) = (cons U (app V W)).

(N x) = (rev V).

(G (rev x) u v) = (app (rev V) (cons U nil)).




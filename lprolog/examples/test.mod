module test.


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
type         app                list int -> int.
type         len                list int -> int.
type         perm               list int -> list int -> bool.
type         nth                int -> list int -> list int.
type         plus               list int -> list int -> list int.
type         minus              int -> int -> int.
type         even               int -> ybool.
type         rot                int -> list int -> list int.

% Meta-level annotations
type         wf                 list int -> list int.
type         wh                 list int -> list int.

% Meta-level variables
type         U                  int.
type         V                  list int.
type         W                  list int.
type         F                  list int -> int -> list int -> list int.

/*
 * Example 1:
 * 
 * perm(U::V,U::W) = perm(u::v,F(rev(rev(v)),u,rev(v))) =>
 * perm(u::v,u::F'(rev(rev(v)),u,rev(v)))
 *
 */

(perm (cons U V) (cons U W)) = (perm (cons u v) (F (rev(rev v)) u (rev v))). 
/*


V = v
U = u
W = Var2 (rev (rev v)) u (rev v)
F = Var3 \ Var4 \ Var5 \ (cons u (Var2 Var3 Var4 Var5)) ;


V = v
U = u
W = Var2 (rev (rev v)) u (rev v)
F = Var6 \ Var7 \ Var8 \ (cons Var7 (Var2 Var6 Var7 Var8)) ;

 */

perm([U|V],[U|W]) = perm([u|v],F(rev(rev(v)),u,rev(v))).
/*
 * V = v
 * U = u
 * W = Var2 (rev (rev v)) u (rev v)
 * F = Var3 \ Var4 \ Var5 \ [u | Var2 Var3 Var4 Var5]
 *
 *
 */

/* 
 * Example 2.
 *
 */

(perm (wf (cons U (wh V))) (wf (cons U (wh W)))) = 
(perm (wf (cons u (wh v))) (wf (F (wh (rev(rev v))) u (rev v)))).

/* 

V = v
U = u
W = Var3 (wh (rev (rev v))) u (rev v)
F = Var4 \ Var5 \ Var6 \ (cons u (wh (Var3 Var4 Var5 Var6))) ;

V = v
U = u
W = rev (rev v)
F = Var7 \ Var8 \ Var9 \ (cons u Var7) ;


V = v
U = u
W = Var10 (wh (rev (rev v))) u (rev v)
F = Var11 \ Var12 \ Var13 \ (cons Var12 (wh (Var10 Var11 Var12 Var13))) ;

V = v
U = u
W = rev (rev v)
F = Var14 \ Var15 \ Var16 \ (cons Var15 Var14) ;

*/

/*
 * Example 3:
 *
 */

(perm v (F (rev (rev v)) u (rev v))) = (perm v (rev(rev v))).

/* 


F = Var3 \ Var4 \ Var5 \ (rev (rev v)) ;

F = Var6 \ Var7 \ Var8 \ (rev Var8) ;

F = W1 \ W2 \ W3 \ W1 ;


*/
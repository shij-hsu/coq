(* Chap 12.1 The Type Hierarchy *)

Check 0.
Check nat.
Check Set.
Check Type.

Set Printing Universes.

Check nat.
Check Type.
Check forall T:Type, T.

Set Implicit Arguments.
Definition id (T:Set) (x:T) :T := x.

Check id 0.
Reset id.

Definition id (T:Type) (x:T) :T := x.
Check id Set.
Check id Type.
(* Check id id. *)

(* Chap 12.1.1 *)

Inductive exp : Type -> Type :=
| Const : forall T : Type, T -> exp T
| Pair : forall T1 T2, exp T1 -> exp T2 -> exp (T1*T2)
| Eq : forall T, exp T -> exp T -> exp bool.

Check Const 0.
Check Pair (Const 0) (Const tt).
Check Eq (Const Set) (Const Type).

Print exp.
Print Universes.
Print prod.

Inductive prod (A:Type)  (B:Type):Type :=
  pair : A->B ->A*B.
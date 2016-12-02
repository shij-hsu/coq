(* This file is used for testing `autorewrite` tactics *)

Reset Initial.
Require Import Arith.
Variable Ack : nat->nat->nat.

Axiom Ack0 : forall m:nat, Ack 0 m = S m.
Axiom Ack1 : forall n:nat, Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall n m:nat, Ack (S n)  (S m) = Ack n (Ack (S n) m).

Hint Rewrite Ack0 Ack1 Ack2 :base0.

Lemma RseAck0 : Ack 3 2 = 29.
  autorewrite with base0 using try reflexivity. Qed.

Require Import Omega.

Variable g : nat->nat->nat.

Axiom g0 : forall m:nat, g 0 m=m.
Axiom g1 : forall n m:nat, (n>0) -> (m>100) -> g n m = g (pred n) (m - 10).
Axiom g2 : forall n m:nat, (n>0)->(m<=100) -> g n m = g (S n) (m+11).

Hint Rewrite g0 g1 g2 using omega:base1.
Lemma Resg0 : g 1 110 = 100.
  autorewrite with base1 using first [progress reflexivity |  progress simpl]. Qed.
(* exp1 || exp2 is equivalent to first [progress exp1 | progress exp2] tactics *)
Lemma Resg1 : g 1 95 = 91.
  autorewrite with base1 using reflexivity || simpl. Qed.


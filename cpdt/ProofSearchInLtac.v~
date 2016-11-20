Require Import Arith.

Ltac find_if:=
  match goal with
  | [|- if ?X then _ else _]=> destruct X
  end.

Theorem hmm : forall (a b c:bool),
    if a
    then if b
         then True
         else True
    else if c
         then True
         else True.
Proof. intros. repeat find_if; constructor. Qed.

Ltac find_if_inside:=
  match goal with
  | [|- context [ if ?X then _ else _]]=> destruct X
  end.

Theorem hmm' : forall (a b c:bool),
    if a
    then if b
         then True
         else True
    else if c
         then True
         else True.
Proof. intros. repeat find_if_inside; constructor. Qed.

Theorem hmm2 : forall (a b c:bool),
    (if a then 42 else 42)=(if b then 42 else 42).
Proof. intros; repeat find_if_inside; constructor. Qed.


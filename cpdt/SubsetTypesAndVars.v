Require Import Arith.
Require Import Cpdt.CpdtTactics.
Print pred.

Extraction pred.

Set Implicit Arguments.

Lemma zgtz : 0>0-> False.
  crush. Qed.

Definition pred_strong1 (n:nat):n>0-> nat :=
match n with
| O => fun pf:0>0 => match zgtz pf with end
| S n' => fun _ => n'
end.

Print pred_strong1.

Theorem two_gt0 : 2>0.
  crush. Qed.

Eval compute in pred_strong1 two_gt0.

Definition pred_strong1' (n:nat):n>0 -> nat:=
  match n return n>0-> nat with
  | O => fun pf:0>0 => match zgtz pf with end
  | S n' => fun _ => n'
  end.

Extraction pred_strong1.
Print sig.


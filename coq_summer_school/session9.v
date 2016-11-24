Require Import ZArith.
Require Import Arith.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition pred_safe : forall x, x<>0 -> nat.
Inductive bnat (n:nat) : Type :=
  cb : forall m , m<n ->bnat n.
Inductive array (n:nat) : Type:=
  ca: forall l:list Z, length l =n -> array n.

Reset bnat.
Definition bnat n := { m | m<n}.
Definition array n := {l:list Z|length l =n}.
Inductive sig (A:Type) (P:A->Prop) : Type := exist: forall x:A, P x-> sig P.
(*
Definition bsucc n:bnat n->bnat (S n) :=
  fun m => let (x,p) := m in
         exist _ (S x) (lt_n_S _ _ p).
 *)
Definition bsucc n:bnat n->bnat (S n).
Proof. intros. destruct H.
   exists (S x).
   auto with arith. Qed. Abort.

Section Test.
  Reset sig. 
  Inductive sig (A:Set) (P:A->Prop) : Set:=
    exist : forall x:A, P x-> sig P.
  Variable div_pair : forall a b:nat, 0<b ->
                               {p:nat*nat | a=(fst p)*b+(snd p) /\ 0<=snd p <b}.
  Implicit Arguments sig [A].


End Test.

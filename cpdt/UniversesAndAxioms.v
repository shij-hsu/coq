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
Set Asymmetric Patterns.

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

Check (nat, (Type, Set)).
Inductive prod': Type->Type->Type:=
| pair' : forall A B:Type, A->B->prod' A B.

(* Check (pair' nat (pair' Type Set)). *)

Inductive foo (A:Type) : Type:=
| Foo : A-> foo A.

Check foo nat.
Check foo Set.
Check foo (foo Set).

Inductive bar   : Type := Bar: bar.
Check bar.

Theorem symmetry : forall A B:Type, A=B -> B=A.
  intros; rewrite H; reflexivity. Qed.

Theorem illustrative_but_silly_detour : unit=unit.
  Set Printing All.
Abort.

Theorem illustrative_but_silly_detour':(unit:Type)=unit.
  apply symmetry; reflexivity. Qed.

Unset Printing All.

Theorem ex_symmetry : (exists x, x=0)->(exists x, 0=x).
  eexists. destruct H. Restart.
  destruct 1 as [x].
  eapply ex_intro. symmetry. eassumption. Qed.

(* 12.2 *)
Print sig.
Print ex.
Print exist.

Definition projS A (P:A->Prop) (x : sig P):A :=
match x with
| exist v _ => v
end.

(*
Definition projE A (P:A->Prop) (x:ex P) : A :=
  match x with
    | ex_intro v _ => v
  end.
 *)

Definition sym_sig (x:sig (fun n=>n =0)) : sig (fun n => 0=n) :=
  match x with
  | exist n pf => exist _ n (sym_eq pf)
  end.
Extraction sym_sig.

Definition sym_ex (x: ex (fun n=> n=0)) : ex (fun n=> 0 =n) :=
  match x with
  | ex_intro n pf => ex_intro _ n (sym_eq pf)
  end.

Extraction sym_ex.

Check forall P Q:Prop, P \/ Q -> Q \/ P.
Inductive expP:Type->Prop :=
| ConstP : forall T, T->expP T
| PairP: forall T1 T2, expP T1-> expP T2->expP (T1*T2)
| EqP : forall T, expP T->expP T ->expP bool.

Check ConstP 0.
Check (PairP (ConstP 0) (ConstP tt)).
Check (EqP (ConstP Set) (ConstP Type)).

Inductive eqPlus: forall T, T->T->Prop:=
| Base : forall T (x:T), eqPlus x x
| Func : forall dom ran (f1 f2:dom->ran),
    (forall x:dom, eqPlus (f1 x) (f2 x)) -> eqPlus f1 f2.

Check (Base 0).
Check (Func (fun n => n) (fun n=> 0+n) (fun n=> Base n)).
Check (Base (Base 1)).

(* 12.3 *)

Require Import Classical_Prop.
Print classic.

Parameter num : nat.
Axiom positive : num>0.
Reset num.

Axiom not_classic : ~ forall P:Prop, P \/ ~P.
Theorem uhoh : False.
  generalize classic not_classic; tauto. Qed.

Theorem uhoh_again : 1+1=3.
  destruct uhoh. Qed.

Reset not_classic.

Theorem t1 : forall P:Prop, P -> ~ ~ P.
  tauto. Qed.

Print Assumptions t1.
Theorem t2 : forall P:Prop, ~ ~ P ->P.
  tauto. Qed.

Print Assumptions t2.

Theorem nat_eq_dec : forall n m:nat, n=m \/ n<>m.
  induction n. destruct m. intuition.
  right. intuition. inversion H.
  destruct m. right. intuition. inversion H.
  destruct (IHn m) eqn:E1.
  - left. rewrite e. reflexivity.
  - right. unfold not. intros. apply n0.
    auto. Qed.

Require Import ProofIrrelevance.

Print proof_irrelevance.
Require Import ZArith.

(*
Definition pred_strong1 (n:nat) : n>0 -> nat:=
  match n with
  | O=> fun pf: 0 > 0 => match Z.zgtz pf with end
  | S n' => fun _ => n'
  end.
 *)

Require Import Eqdep.
Import Eq_rect_eq.
Print Eq_rect_eq.

Corollary UIP_refl : forall A (x:A) (pf: x=x), pf=eq_refl x.
  intros; replace pf with (eq_rect x (eq x) (eq_refl x) x pf);
    [symmetry; apply eq_rect_eq
    | exact (match pf as pf' return match pf' in _ = y return x=y with
                                    | eq_refl => eq_refl x
                                    end = pf' with
             | eq_refl => eq_refl _
             end)]. Qed.

Corollary UIP : forall A (x y:A) (pf1 pf2:x=y), pf1=pf2.
  intros; generalize pf1 pf2;subst;intros;
    match goal with
    | [ |- ?pf1 = ?pf2] => rewrite (UIP_refl pf1); rewrite (UIP_refl pf2); reflexivity
    end. Qed.

Require Import FunctionalExtensionality.
Print functional_extensionality_dep.
Corollary predicate_extensionality : forall (A:Type) (B:A->Prop) (f g:forall x:A, B x),
    (forall x:A, f x=g x) -> f=g.
  intros. apply functional_extensionality_dep; assumption. Qed.

(* 12.3.2 *)

Require Import ConstructiveEpsilon.
Check constructive_definite_description.
Print Assumptions constructive_definite_description.

Require Import ClassicalUniqueChoice.
Check dependent_unique_choice.
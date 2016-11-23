(* Chap13 Introducing Logic Progamming *)

Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

Set Implicit Arguments.
Set Asymmetric Patterns.

Print plus.
Inductive plusR  : nat ->nat -> nat->Prop :=
| PlusO :forall m, plusR O m m
| PlusS : forall n m r, plusR n m r ->plusR (S n) m (S r).

Hint Constructors plusR.

Theorem plus_plusR : forall n m, plusR n m (n+m).
  induction n; crush. Qed.

Example four_plus_three: 4+3=7.
reflexivity. Qed.

Print four_plus_three.

Example four_plus_three': plusR 4 3 7.
apply PlusS. apply PlusS. apply PlusS. apply PlusS. apply PlusO.
Restart. auto. Qed.

Print four_plus_three'.
Example five_plus_three: plusR 5 3 8.
auto. auto 6.
Restart. info_auto 6. Qed.

Example seven_minus_three: exists x, x+3=7.
apply ex_intro with 0. 
Restart. apply ex_intro with 4. reflexivity. Qed.

Example seven_minus_three' : exists x, plusR x 3 7.
eapply ex_intro.
apply PlusS. apply PlusS.
apply PlusS.
apply PlusS. apply PlusO.
Restart. info_eauto 6. Qed.

Example seven_minus_four' : exists x, plusR 4 x 7.
eauto 6. Qed.

SearchRewrite ( O + _).
Hint Immediate plus_O_n.

Lemma plusS : forall n m r, n+m=r-> S n+m=S r.
  crush. Qed.

Hint Resolve plusS.
Example seven_minus_three'': exists x, x+3=7.
eauto 6. Qed.

Example seven_minus_four: exists x, 4+x=7.
eauto 6. Qed.

Example seven_minus_zero: exists x, 4+x+0 =7.
eauto 6. Abort.

Lemma plusO : forall n m, n=m->n+0=m. crush. Qed.

Hint Resolve plusO.

Example seven_minus_four_zero : exists x, 4+x+0 =7.
eauto 7. Qed.

Check eq_trans.

Section slow.
  Hint Resolve eq_trans.
  Example zero_minus_one : exists x, 1+x=0.
  Time eauto 1.
  Time eauto 2.
  Time eauto 3.
  Time eauto 4.
  Time eauto 5.

  debug eauto 3.
  Abort.
End slow.

Hint Resolve eq_trans: slow.
Example from_one_to_zero : exists x, 1+x=0.
Time eauto. Abort.

Example seven_minus_three_again : exists x, x+3=7.
Time eauto 6. Qed.

Example needs_trans : forall x y, 1+x=y
                             -> y=2 -> exists z, z+x=3.

info_eauto with slow.
Qed.

(* Chap13.2 *)

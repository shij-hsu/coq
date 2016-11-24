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
Require Import List.

Print length.

Example length_1_2 :  length (1::2::nil)=2.
auto. Qed.

Print length_1_2.
Theorem length_O : forall A, length (nil (A:=A))=O.
  crush. Qed.
Theorem length_S : forall A (h:A) t n,
    length t=n -> length (h::t) = S n.
  crush. Qed.
Hint Resolve length_O length_S.

Example length_is_2 : exists ls:list nat, length ls=2.
eauto. Show Proof. Abort.

Print Forall.
Example length_is_2:  exists ls:list nat, length ls=2
                                   /\ Forall (fun n=>n>=1) ls.
eauto 9. Qed.
Print length_is_2.
Definition sum := fold_right plus O.

Lemma plusO' : forall n m, n=m -> 0+n=m.
  crush. Qed.

Hint Resolve plusO'.
Hint Extern 1 (sum _ = _) => simpl.

Example length_and_sum : exists ls:list nat, length ls=2
                                      /\ sum ls=O.
eauto 7. Qed.

Example length_and_sum' : exists ls:list nat, length ls=5 /\ sum ls=42.
eauto 15. Qed.

Example length_and_sum'' : exists ls: list nat, length ls=2
                                         /\ sum ls=3
                                         /\ Forall (fun n=> n<> 0) ls.
eauto 11. Qed.

(* chap13.3 *)
Inductive exp:Set:=
| Const:nat->exp
| Var:exp
| Plus : exp->exp ->exp.

Inductive eval (var:nat) : exp->nat->Prop:=
| EvalConst : forall n, eval var (Const n) n
| EvalVar: eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1->
                            eval var e2 n2->
                            eval var (Plus e1 e2) (n1+n2).
Hint Constructors eval.

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + ( 8+var)).
auto. Qed.
Example eval1': forall var, eval var (Plus Var (Plus (Const 8) Var)) (2*var+8).
eauto. Abort.

Theorem EvalPlus' : forall var e1 e2 n1 n2 n, eval var e1 n1->
                                         eval var e2 n2 ->
                                         n1+n2=n->
                                         eval var (Plus e1 e2) n.
  crush. Qed.

Hint Resolve EvalPlus'.

Hint Extern 1 ( _ = _ ) => abstract omega.

Example eval1': forall var, eval var (Plus Var (Plus (Const 8) Var)) (2*var+8).
eauto. Qed.
Print eval1'.

Example synthesize1:exists e, forall var, eval var e (var +7).
eauto. Qed.

Print synthesize1.

Example synthesize2:exists e,forall var, eval var e (2*var+8).
eauto. Qed.
Example synthesize3:exists e, forall var, eval var e (3*var+42).
eauto. Qed.

Theorem EvalConst' :forall var n m, n=m->
                               eval var (Const n) m.
  crush. Qed.
Hint Resolve EvalConst'.

Theorem zero_times : forall n m r, r=m->
                              r=0*n+m.
  crush. Qed.

Hint Resolve zero_times.
Theorem EvalVar' : forall var n, var=n ->eval var Var n.
  crush. Qed.

Hint Resolve EvalVar'.
Theorem plus_0 : forall n r, r=n ->r = n+0.
  crush. Qed.

Theorem times_1 : forall n, n=1*n.
  crush. Qed.
Hint Resolve times_1 plus_0.

Require Import Arith Ring.
Theorem combine : forall x k1 k2 n1 n2,
    (k1*x+n1)+(k2*x+n2)=(k1+k2)*x+(n1+n2).
  intros; ring. Qed.

Hint Resolve combine.
Theorem linear : forall e, exists k, exists n, forall var, eval var e (k*var +n).
  induction e; crush; eauto. Qed.

(* 13.4 *)

Theorem bool_neq : true <> false.
  auto. Abort.
Hint Extern 1 ( _ <> _) => congruence.

Theorem bool_neq : true <> false.
  auto. Qed.

Section forall_and.
  Variable A : Set.
  Variables P Q:A->Prop.

  Hypothesis both: forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
    crush.
    Hint Extern 1 (P ?X) =>
    match goal with
      | [ H:forall x, P x /\ _ |- _]=> apply (proj1 (H X))
    end.
    auto. Qed.

End forall_and.
  Hint Extern 1 =>
  match goal with
    | [ H: forall x, ?P x /\ _ |- ?P ?X]=> apply (proj1 (H X))
  end.

  (* 13.5 *)

  Section autorewrite.
    Variable A : Set.
    Variable f : A->A.

    Hypothesis f_f: forall x, f (f x)=f x.
    Hint Rewrite f_f.
    
    Lemma f_f_f : forall x, f (f (f x))=f x.
      intros; autorewrite with core; reflexivity. Qed.

    Section garden_path.
      Variable g : A->A.
      Hypothesis f_g : forall x, f x=g x.

      Hint Rewrite f_g.
      Lemma f_f_f' : forall x, f (f (f x)) = f x.
        intros; autorewrite with core. Abort.
      Reset garden_path.
      Section garden_path.
        Variable P : A->Prop.
        Variable g : A->A.

        Hypothesis f_g : forall x, P x->f x=g x.
        Hint Rewrite f_g.

        Lemma f_f_f' : forall x, f (f (f x))=f x.
          intros; autorewrite with core. Abort.

        Reset garden_path.
      Section garden_path.
        Variable P : A->Prop.
        Variable g : A->A.

        Hypothesis f_g : forall x, P x->f x=g x.
        Hint Rewrite f_g using assumption.

        Lemma f_f_f' : forall x, f (f (f x))=f x.
          intros; autorewrite with core; reflexivity. Qed.

        Lemma f_f_f_g : forall x, P x->f (f x)=g x.
          intros; autorewrite with core; reflexivity. Qed.
      End garden_path.

      Hint Rewrite f_f_f_g using assumption.
      Lemma in_star : forall x y, f (f (f (f x)))=f (f y).
        intros; autorewrite with core in *. Abort. 
  End autorewrite.

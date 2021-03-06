Require Import Arith.

Theorem t5 : (forall x:nat, S x>x )->2 >1.
  intro H. evar (y : nat).
  let y':=eval unfold y in y in
      clear y; specialize (H y').
  apply H. Qed.

Ltac insterU H:=
  repeat match type of H with
         |  forall x:?T , _ =>
           let x:= fresh "x" in
           evar (x:T);
           let x':= eval unfold x in x in
               clear x; specialize (H x')
         end.

Theorem t5' : (forall x, S x> x)->2 >1.
  intro H; insterU H; apply H. Qed.

Ltac insterKeep H:=
  let H':=fresh "H'" in
  generalize H; intro H'; insterU H'. (* 从H生成一个较弱的条件，同时保留H*)

Section t6.
  Variables  A B:Type.
  Variable P : A->B->Prop.
  Variable f: A->A->A.
  Variable g : B->B->B.

  Hypothesis H1:forall v, exists u, P v u.
  Hypothesis H2:forall v1 u1 v2 u2,
      P v1 u1->
      P v2 u2->
      P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros. do 2 insterKeep H1.
    repeat match goal with
           | [ H : ex _ |- _]=> destruct H
           end; eauto. Qed.
End t6.

Section t7.
  Variables A B:Type.
  Variable Q : A->Prop.
  Variable P : A->B->Prop.
  Variable f : A->A->A.
  Variable g : B->B->B.

  Hypothesis H1:forall v, Q v->exists u, P v u.
  Hypothesis H2:forall v1 u1 v2 u2,
      P v1 u1 ->
      P v2 u2->
      P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1->Q v2-> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros. do 2 insterKeep H1.
    repeat match goal with
           | [H: ex _ |- _]=>destruct H
           end;eauto. Abort.
End t7.

Reset insterU.
Ltac insterU tac H:=
  repeat match type of H with
         | forall x:?T, _ =>
           match type of T with
           | Prop =>
             (let  H':= fresh "H'" in
              assert (H':T) by solve[tac];
              specialize (H H'); clear H')
             || fail 1
           | _ =>
             let x:=fresh "x" in
             evar (x:T);
             let x':=eval unfold x in x in
                 clear x; specialize (H x')
           end
         end.

Ltac insterKeep tac H:=
  let H':= fresh "H'" in
  generalize H; intro H'; insterU tac H'.

Section t7.
  Variable A B:Type.
  Variable Q : A->Prop.
  Variable P : A->B->Prop.
  Variable f : A->A->A.
  Variable g : B->B->B.

  Hypothesis H1:forall v, Q v->exists u, P v u.
  Hypothesis H2:forall v1 u1 v2 u2,
      P v1 u1->
      P v2 u2->
      P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 ->Q v2 ->exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep ltac:(idtac; match goal with
                                         | [H: Q ?v |- _]=>
                                           match goal with
                                           | [ _:context[P v _]|- _]=>fail 1
                                           | _ => apply H
                                           end
                                         end) H1.
    repeat match goal with
             | [H:ex _ |- _]=>destruct H
           end; eauto. Qed.
End t7.

Theorem t8: exists p:nat*nat, fst p=3.
  econstructor. instantiate (1:=(3,2)). reflexivity. Qed.

Theorem t8' : exists (a b:nat), fst (a,b) =3 /\ snd (a,b) =2.
  econstructor. econstructor. instantiate (1:=2).
  instantiate (1:=3). constructor; reflexivity. Qed.

Ltac equate x y:=
  let dummy:=constr:(eq_refl x: x=y) in idtac.

Theorem t9 : exists p:nat*nat, fst p=3.
  econstructor.
  match goal with
    | [|- fst ?x = 3]=> equate x (3,2)
  end; reflexivity. Qed.

Theorem t9' : exists p:nat*nat, fst p=3.
  econstructor. instantiate(1:=(3,2)). idtac. reflexivity. Qed.


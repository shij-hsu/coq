Require Import Coq.Setoids.Setoid.


(* 0.1 From Inductive Types *)

(* exercise 1 *)
Inductive truth:Type:= Yes|No|Maybe.

Definition not (a:truth):truth :=
  match a with
  | Yes => No
  | No => Yes
  | Maybe => Maybe
  end.

Check not Yes.

Definition and (a b:truth):truth:=
match a with
| Yes => b
| No => match b with
       | Maybe => Maybe
       | _ => No
       end
| Maybe => Maybe
end.

Definition or (a b:truth):truth :=
  match a with
  | Yes => match b with
          | Maybe => Maybe
          | _ => Yes
          end
  | No => b
  | Maybe => Maybe
  end.

Lemma and_comm : forall (a b:truth), and a b = and b a.
  intros; destruct a, b; auto. Qed.
Lemma or_comm : forall (a b:truth), or a b = or b a.
  intros; destruct a, b; auto. Qed.
Lemma or_distr : forall (a b c:truth), or (and a b) c=and (or a c) (or b c).
  intros; destruct a, b, c; auto. Qed.

(* exercise 2 *)

Require Import List.
Set Implicit Arguments.
Inductive slist (X:Type): Type:=
| s_nil:slist X
| s_singleton:X-> slist X
| s_cons: slist X-> slist X-> slist X.

Fixpoint flattern (X:Type) (sl:slist X):list X :=
  match sl with
  | @s_nil _ => nil
  | s_singleton a => a::nil
  | s_cons sl1 sl2 => (flattern sl1)++(flattern sl2)
  end.
Fixpoint s_app (X:Type) (s1 s2:slist X):slist X:=
  match s1 with
  | @s_nil _=> s2
  | s_singleton a' as a => s_cons a s2
  | s_cons a s1' => s_cons a (s_app s1' s2)
  end.
Lemma flattern_distr : forall (X:Type) (a b:slist X), flattern (s_app a b)=(flattern a)++(flattern b).
  induction a; intuition.
  - simpl. rewrite <-app_assoc. rewrite <-(IHa2 b). reflexivity. Qed.

(* exercise 3 *)

Inductive binop : Set:=Plus | Times | Assgn.
Inductive exp : Set :=
| Const :nat-> exp
| Binop:binop-> exp-> exp-> exp
| Var:nat-> exp.

Definition binopDenote (b:binop):nat-> nat-> nat :=
match b with
| Plus => plus
| Times => mult
| Assgn => fun _ n => n
end.

Fixpoint expDenote (e:exp):nat:=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  | Var n => n
  end.

Eval
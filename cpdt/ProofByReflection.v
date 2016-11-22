(* chap 15.1 Proving Eveness *)
Set Implicit Arguments.
Set Asymmetric Patterns.


Inductive isEven  : nat->Prop :=
| Even_O: isEven O
| Even_SS:forall n, isEven n->isEven (S (S n)).

Ltac prove_even:= repeat constructor.
Theorem even_256 : isEven 256.
  prove_even. Qed.
Theorem lt_2_1024 : 2<256.  (* it will be very slow *)
  prove_even. Qed.

Print lt_2_1024.
Print even_256.

Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

Print partial.
Local Open Scope partial_scope.
Definition check_even: forall n:nat, [isEven n].
  Hint Constructors isEven.
  refine (fix F (n:nat):[isEven n]:=
            match n with
            | 0=>Yes
            | 1=>No
            | S (S n')=>Reduce (F n')
            end); auto.
Defined.

Definition partialOut (P:Prop) (x:[P]) :=
match x return (match x with
                | Proved _ =>P
                | Uncertain =>True
                end) with
| Proved pf => pf
| Uncertain => I
end.


Ltac prove_even_reflective:=
  match goal with
  | [ |- isEven ?N ]=> exact (partialOut (check_even N))
  end.

Theorem even_256' : isEven 256.
 prove_even_reflective. Qed.

Print even_256'.

Theorem even_255 : isEven 255.
Abort.

(* chap 15.2 *)

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
  tauto. Qed.
Print true_galore.

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut->taut->taut
| TautOr: taut->taut->taut
| TautImp: taut ->taut ->taut.

Fixpoint tautDenote (t:taut) : Prop :=
  match t with
  | TautTrue => True
  | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
  | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
  | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

Theorem tautTrue : forall t, tautDenote t.
  induction t; crush. Qed.

Ltac tautReify P :=
  match P with
  | True => TautTrue
  | ?P1 /\ ?P2 =>
    let t1:= tautReify P1 in
    let t2:=tautReify P2 in
    constr:(TautAnd t1 t2)
  | ?P1 \/ ?P2 =>
    let t1:= tautReify P1 in
    let t2:= tautReify P2 in
    constr:(TautOr t1 t2)
  | ?P1 -> ?P2 =>
    let t1:= tautReify P1 in
    let t2:= tautReify P2 in
    constr:(TautImp t1 t2)
  end.

Ltac obvious :=
  match goal with
  | [ |- ?P ]=>
    let t:=tautReify P in
    exact (tautTrue t)
  end.

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
  obvious. Qed.

Print true_galore'.


(* chap 15.3 *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A->A->A.

  Infix "+" := f.
  Hypothesis assocc:forall a b c, (a+b)+c =a +(b+c).
  Hypothesis identl :forall a, e+a= a.
  Hypothesis identr: forall a, a+e=a.

  Inductive mexp:Set:=
  | Ident:mexp
  |Var :A -> mexp
  | Op : mexp ->mexp ->mexp.

  Fixpoint mdenote (me:mexp) : A:=
    match me with
    | Ident => e
    | Var v => v
    | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  Require Import List.
  Fixpoint mIdenote (ls :list A): A:=
    match ls with
    | nil => e
    | x::ls'=> x+ mIdenote ls'
    end.

  Fixpoint flatten (me:mexp) :list A:=
    match me with
    | Ident => nil
    | Var x => x::nil
    | Op me1 me2 =>flatten me1++flatten me2
    end.

  Lemma flatten_correct': forall ml2 ml1,
      mIdenote ml1 + mIdenote ml2 = mIdenote (ml1++ml2).
    induction ml1; crush. Qed.

  Theorem flatten_correct : forall me, mdenote me = mIdenote (flatten me).
    Hint Resolve flatten_correct'.
    induction me; crush. Qed.

  Theorem monoid_reflect : forall me1 me2, mIdenote (flatten me1) =
                                      mIdenote (flatten me2) ->
                                      mdenote me1=mdenote me2.
    intros; repeat rewrite flatten_correct; assumption. Qed.

  Ltac reify me:=
    match me with
    | e => Ident
    | ?me1 + ?me2 =>
      let r1:= reify me1 in
      let r2:= reify me2 in
      constr:(Op r1 r2)
    | _ => constr:(Var me)
    end.

  Ltac monoid :=
    match goal with
    | [ |- ?me1 = ?me2 ]=>
      let r1:= reify me1 in
      let r2:= reify me2 in
      change (mdenote r1=mdenote r2);
      apply monoid_reflect; simpl
    end.

  Theorem t1:forall a b c d, a+b+c +d = a+ (b+c) +d.
    intros; monoid. reflexivity. Qed.

  Print t1.

  End monoid.
(* chap 15.1 Proving Eveness *)

Require Import List.
Require Import Cpdt.CpdtTactics Cpdt.MoreSpecif.

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

Lemma true_test1: True.
  exact (tautTrue TautTrue). Qed.
Print true_test1.
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

Module test1. (* This module is a test for keyword `return` *)
  Inductive test:Type:=
    test1 | test2.
  Definition return_test (n:test) :=
    match n return (match n with
                    | test1 => Prop
                    | test2 => Type
                   end)  with
    | test1 => (forall x:nat , x >=0)
    | test2 => test
    end.
  Lemma test_test : return_test test1=(forall x:nat, x >= 0).
    reflexivity. Qed. Print test_test.
End test1.

(* chap 15.4 *)
Require Import Quote.

Inductive formula: Set:=
| Atomic :index->formula
| Truth: formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or: formula -> formula -> formula
| Imp : formula -> formula -> formula.

Definition imp (P1 P2:Prop)  := P1->P2.
Infix "->" := imp (no associativity, at level 95).

Definition asgn := varmap Prop.
Fixpoint formulaDenote (atomics:asgn) (f:formula) :Prop:=
  match f with
  | Atomic v => varmap_find False v atomics
  | Truth => True
  | Falsehood => False
  | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
  | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
  | Imp f1 f2 => formulaDenote atomics f1 -> formulaDenote atomics f2
  end.

Section my_tauto.
  Variable atomics : asgn.
  Definition holds (v:index)  := varmap_find False v atomics.
  Require Import ListSet.

  Definition index_eq : forall x y:index, {x = y}+{ x<> y}.
    decide equality.
  Defined.

  Definition add (s:set index) (v:index)  := set_add index_eq v s.
  Definition In_dec:forall v (s :set index), {In v s}+{~ In v s} .
    Local Open Scope specif_scope.

    intro; refine (fix F (s:set index) : {In v s}+{~ In v s}:=
                     match s with
                     | nil => No
                     | v'::s' => index_eq v' v || F s'
                     end); crush.
  Defined.

  Fixpoint allTrue (s:set index) :Prop:=
    match s with
    | nil => True
    | v::s' => holds v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s, allTrue s->
                               holds v->allTrue (add s v).
    induction s; crush; match goal with
                        | [ |- context[if ?E then _ else _]]=> destruct E
                        end; crush. Qed.

  Theorem allTrue_In : forall v s, allTrue s -> set_In v s ->
                              varmap_find False v atomics.
    induction s; crush. Qed.

  Hint Resolve allTrue_add allTrue_In.
  Local Open Scope partial_scope.

  Definition forward: forall (f :formula) (known:set index) (hyp:formula)
                        (cont: forall known', [allTrue known'->formulaDenote atomics f]),
      [allTrue known ->formulaDenote atomics hyp -> formulaDenote atomics f].
    refine (fix F (f:formula ) (known: set index) (hyp: formula)
                (cont : forall known', [allTrue known' -> formulaDenote atomics f])
            : [ allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f]:=
              match hyp with
              | Atomic v => Reduce (cont (add known v))
              | Truth => Reduce (cont known)
              | Falsehood  => Yes
              | And h1 h2 =>
                Reduce (F (Imp h2 f) known h1 (fun known' =>
                                                 Reduce (F f known' h2 cont)))
              | Or h1 h2 => F f known h1 cont && F f known h2 cont
              | Imp _ _ => Reduce (cont known)
              end); crush.
  Defined.

  Definition backward : forall (known : set index) (f : formula),
[allTrue known -> formulaDenote atomics f ].
refine (fix F (known : set index) (f : formula)
: [allTrue known -> formulaDenote atomics f ] :=
match f with
| Atomic v => Reduce (In_dec v known)
| Truth => Yes
| Falsehood => No
| And f1 f2 => F known f1 && F known f2
| Or f1 f2 => F known f1 || F known f2
| Imp f1 f2 => forward f2 known f1 (fun known' => F known' f2 )
end); crush; eauto.
  Defined.

  Definition my_tauto: forall f: formula, [formulaDenote atomics f].
    intro; refine (Reduce (backward nil f)) ;crush. Defined.

End my_tauto.

Ltac my_tauto:=
  repeat match goal with
         | [ |- forall x:?P, _ ]=>
           match type of P with
           | Prop => fail 1
           | _ => intro
           end
         end;
  quote formulaDenote;
  match goal with
  | [ |- formulaDenote ?m ?f] => exact (partialOut (my_tauto m f))
  end.

Theorem mt1 : True.
  my_tauto. Qed.

Print mt1.

Theorem mt2 : forall x y:nat, x= y -> x=y.
  intros.  
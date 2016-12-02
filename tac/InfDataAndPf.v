Require Import Arith.
Set Implicit Arguments.

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
    | Cons : A->stream->stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.
CoFixpoint trues_falses : stream bool := Cons true falses_trues
with falses_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | Cons h t => h::approx t n'
    end
  end.

Eval simpl in approx zeroes 10.

Eval simpl in approx trues_falses 10.

CoFixpoint looper : stream nat := looper.
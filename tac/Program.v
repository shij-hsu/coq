Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Arith Bool.
Program Fixpoint div2 (n:nat) {measure n}: {x:nat | n=2*x \/ n=2*x+1} :=
  match n with
  | S (S p) => S (div2 p)
  | _ => O
  end.
Fixpoint leb (n m:nat) :=
  match n with
  | O => true
  | S n' => match m with
           | O => false
           | S m' => leb n' m'
           end
  end.

Program Definition id (n:nat) : { x:nat | x=n} :=
  if (leb n 0) then 0 else S (pred n).

Definition pplus :=
fun (n m:nat) => plus n m.

Extraction Language Haskell.
Extraction "id.hs" pplus.
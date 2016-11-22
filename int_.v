Require Import Arith.

Inductive div:nat->nat->Prop:=
|div_n_n:forall n:nat, div n n
|div_add:forall (n m:nat), div n m->div n (m+n).


Ltac insterU H:=
  repeat match type of H with
         | forall x:?T, _ =>
           let y:=fresh "y" in
           evar (y : nat);
           let y':= eval unfold y in y in specialize (H y'); clear y
         end.
  
Lemma lt_1000_1:1000>2.
Proof. assert (H:forall x,S x>x).
   { intros. apply le_n. }
   

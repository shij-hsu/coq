Require Arith.
Require Bool.
Require Compare_dec.

Inductive maxn (f:nat->nat):nat->nat->Prop :=
  maxnO: (maxn f O (f O))
 |maxnSg : forall n m:nat, (maxn f n m)->(ge m (f (S n)))->(maxn f (S n) m)
 |maxnSl : forall n m:nat, (maxn f n m) -> (le m (f (S n)))-> (maxn f (S n) (f (S n))).

Lemma nat_well_ordered : forall n m:nat, le n m \/ ge n m.
  induction n.
  - intros. left. apply le_0_n.
  - destruct m. right. apply le_0_n.
    destruct (IHn m).
    + left; apply le_n_S. assumption.
    + right; apply le_n_S. assumption. Qed.
Lemma max_val : forall (f:nat->nat) (n:nat), exists m:nat, maxn f n m.
  intros f; induction n.
  - exists (f O). apply maxnO.
  - destruct IHn as [m]; destruct (nat_well_ordered m (f (S n))).
    * exists (f (S n)). eapply maxnSl. eassumption. assumption.
    * exists m. eapply maxnSg. assumption. assumption. Qed.

Extraction Language Haskell.
Extraction "maxv" max_val.
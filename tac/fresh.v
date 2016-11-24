Theorem t5 : (forall x:nat, S x> x)-> 2>1.
  intros.
  let H':=fresh "H'" in generalize H.
  intros H'. auto. Qed.

Theorem t5' : (forall x:nat, S x>x ) -> 2>1.
  intros H.
  let H':=fresh "H" in apply (H' 1). Qed.
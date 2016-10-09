Require Import Arith.
Require Import List.

Inductive rbtree:Type:=
|NULL:rbtree
|RBTree (key:nat) (color:nat) (p l r:rbtree).

Fixpoint rbtree2list (r:rbtree):list nat:=
  match r with
    |NULL=>nil
    |RBTree key _ _ l r=>key::(rbtree2list l)++(rbtree2list r)
  end.

Eval vm_compute in
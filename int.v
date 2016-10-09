Inductive natural:=
|Zero:natural
|Succ:natural->natural.

Fixpoint add (n:natural) (m:natural):natural:=
  match n with
  |Zero=>m
  |Succ n'=>Succ (add n' m)
  end.
Fixpoint mul (n:natural) (m:natural):natural:=
  match n with
  |Zero=>Zero
  |Succ n'=>add m (mul n' m)
  end.


(*This is some lemmas for natural*)
Lemma add_zero_r:forall (n:natural),add n Zero=n.
  induction n.
  simpl;reflexivity.
  simpl; rewrite IHn;reflexivity.
Qed.

Lemma mul_zero_r:forall (n:natural), mul n Zero=Zero.
  induction n.
  simpl;reflexivity.
  simpl;rewrite IHn;reflexivity.
Qed.

Lemma add_induc_r:forall (n m:natural),add n (Succ m)=Succ (add n m).
  induction n.
  simpl;reflexivity.
  intros;simpl.
  rewrite IHn;reflexivity.
Qed.

Lemma mul_one_l:forall (n:natural),mul (Succ Zero) n=n.
  intros;simpl;rewrite add_zero_r;reflexivity.
Qed.
(*加法交换律*)
Theorem add_comm:forall (n m:natural),add n m=add m n.
Proof.
  induction n.
  intros m.
  rewrite add_zero_r;reflexivity.
  intros;simpl.
  rewrite add_induc_r.
  rewrite IHn.
  reflexivity.
Qed.
(*加法结合律*)
Theorem add_assoc:forall (n m l:natural),add (add n m) l=add n (add m l).
Proof.
  induction n;intros;simpl.
  reflexivity.
  rewrite IHn;reflexivity.
Qed.

Lemma mul_induc_r:forall (n m:natural),mul n (Succ m)=add (mul n m) n.
  induction n.
  intros;simpl;reflexivity.
  intros;simpl.
  rewrite IHn.
  rewrite add_induc_r.
  rewrite add_assoc.
  reflexivity.
Qed.

Lemma mul_one_r:forall (n:natural),mul n (Succ Zero)=n.
  intros;simpl;rewrite mul_induc_r.
  rewrite mul_zero_r;simpl;reflexivity.
Qed.

Lemma mul_comm:forall (n m:natural),mul n m=mul m n.
  induction n.
  intros;simpl.
  rewrite mul_zero_r;reflexivity.
  intros;simpl.
  rewrite mul_induc_r.
  rewrite add_comm.
  rewrite IHn;reflexivity.
Qed.
(*乘法分配律*)
Theorem mul_distr:forall (n m l:natural),mul (add n m) l=add (mul n l) (mul m l).
Proof.
  induction l.
  intros;simpl.
  repeat rewrite mul_zero_r.
  simpl;reflexivity.
  repeat rewrite mul_induc_r;simpl.
  repeat rewrite IHl.
  rewrite add_assoc.
  pattern (add (mul m l) (add n m)) at 1;rewrite add_comm.
  pattern (add (add n m) (mul m l)) at 1;rewrite add_assoc.
  rewrite<-add_assoc.
  pattern (add m (mul m l)) at 1;rewrite add_comm;reflexivity.
Qed.

(*乘法结合律*)
Theorem mul_assoc:forall (n m l:natural),mul (mul n m) l=mul n (mul m l).
Proof.
  induction n.
  intros;simpl;reflexivity.
  intros;simpl.
  rewrite mul_distr.
  rewrite IHn;reflexivity.
Qed.
(*全序性*)
<<<<<<< HEAD
=======
Inductive le_natural (n:natural):natural->Prop:=
|le_natural_n:le_natural n n
|le_natural_S:forall (m:natural),(le_natural n m)->(le_natural n (Succ m)).
>>>>>>> 86ae0ba47d75927e7986114f47492f1ae3d33657

(*数论部分*)
Definition div (n m:natural):Prop:=
  exists p:natural,mul n p=m.

Lemma mul_div (n:natural):forall (p:natural),div n (mul n p).
  intros.
  exists p;reflexivity.
Qed.

Lemma div_n (n:natural):div n n.
  intros;simpl.
  assert (mul n (Succ Zero)=n).
  rewrite mul_one_r;simpl;reflexivity.
  exists (Succ Zero).
  rewrite mul_one_r;simpl;reflexivity.
Qed.



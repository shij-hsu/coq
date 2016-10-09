Require Import Arith.
Open Scope nat_scope.

Fixpoint fact (n:nat):nat:=
  match n with
  |O=>1
  |S n'=>n*fact n'
  end.

Eval vm_compute in fact 8.
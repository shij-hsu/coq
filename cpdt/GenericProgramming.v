(* 11.1 Reifying Datatype Definitions *)


Record constructor : Type :=
  Con{
      nonrecursive : Type;
      recursive : nat
    }.
Definition datatype := list constructor.
Definition Empty_set_dt : datatype := nil.
Definition unit_dt : datatype := Con unit 0::nil.
Require Import List.
Require Import Arith.

Fixpoint split A (l:list A):list A*list A:=
  match l with
  |nil=>(nil,nil)
  |a::nil=>(a::nil,nil)
  |a::b::l'=>let (l1,l2):=split A l' in (a::l1,b::l2)
  end.


Definition merge A (less:A->A->bool)
:list A->list A->list A:=
  fix merge l1:=match l1 with
               |nil=>(fun l2=>l2)
               |x1::l1'=>
                (fix merge_l1 l2:=match l2 with
                                  |nil=>l1
                                  |x2::l2'=>
                                   if less x1 x2 then x1::merge l1' l2
                                   else x2::merge_l1 l2'
                                  end)
               end.
Definition mergeloop A (less:A->A->bool):=
  fix loop (l:list A) (n:nat):=
    match n with
    |O=>nil
    |S n=>match l with
          |nil=>l
          |_::nil=>l
          |_=>let (l1,l2):=split A l in merge A less (loop l1 n) (loop l2 n)
          end
    end.

Definition mergesort A less (l:list A):=
  mergeloop A less l (length l).
<<<<<<< HEAD

Eval vm_compute in mergesort nat leb (1::2::4::1::5::7::3::100::101::nil).
=======
(* Eval vm_compute in mergesort nat leb (1::2::4::1::5::7::3::100::101::nil). *)

Inductive list_in_order A (less:A->A->bool) (l:list A):Prop:=
|empty_in_order:list_in_order A less nil
|one_elem_order:forall (x:A),list_in_order A less x::nil
|list_in_order_induc:forall (x y:A) (l':list A),(less x y)->(list_in_order A less x::y::l').


Lemma list_in_order:forall A (l:list A) (less:A->A->bool),
>>>>>>> 86ae0ba47d75927e7986114f47492f1ae3d33657

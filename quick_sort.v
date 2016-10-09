Require Import Arith.
Require Import List.


Fixpoint split A (l:list A) :list A*list A:=
  match l with
  |nil=>(nil,nil)
  |a::nil=>(a::nil,nil)
  |a::b::l'=>let (l1,l2):=split A l' in (a::l1,b::l2)
  end.

Fixpoint partition A (less:A->A->bool) (mid:A) (l:list A):list A*list A:=
  match l with
  |nil=>(nil,nil)
  |a::l'=>let (l1,l2):=partition A less mid l' in
          if less a mid then (a::l1,l2)
          else (l1,a::l2)
  end.

Fixpoint pluslist A (l1:list A) (l2:list A):=
  match l1 with
  |nil=>l2
  |a::l'=>a::(pluslist A l' l2)
  end.

Definition quicksortloop A (less:A->A->bool):=
  fix loop (l:list A) (n:nat):=
    match n with
    |O=>nil
    |S n=>match l with
          |nil=>l
          |x::l'=>let (l1,l2):=partition A less x l' in
                  pluslist A (loop l1 n) (x::(loop l2 n))
          end
    end.


Definition quicksort A less (l:list A):=
  quicksortloop A less l (length l).

Eval vm_compute in quicksort nat leb (2::1::3::10::100::59::1::0::nil).
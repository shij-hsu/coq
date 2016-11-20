Require Import Arith.
Require Import List.
Require Import Lists.List.

(* chap 14.2 
Ltac Programming Basics
*)
Ltac find_if:=
  match goal with
  | [|- if ?X then _ else _]=> destruct X
  end.

Theorem hmm : forall (a b c:bool),
    if a
    then if b
         then True
         else True
    else if c
         then True
         else True.
Proof. intros. repeat find_if; constructor. Qed.

Ltac find_if_inside:=
  match goal with
  | [|- context [ if ?X then _ else _]]=> destruct X
  end.

Theorem hmm' : forall (a b c:bool),
    if a
    then if b
         then True
         else True
    else if c
         then True
         else True.
Proof. intros. repeat find_if_inside; constructor. Qed.

Theorem hmm2 : forall (a b c:bool),
    (if a then 42 else 42)=(if b then 42 else 42).
Proof. intros; repeat find_if_inside; constructor. Qed.

Ltac my_tauto:=
  repeat match goal with
         | [H: ?P|-?P]=>exact H
         | [|-True]=>constructor
         | [|- _ /\ _ ]=>constructor
         | [|- _ -> _]=>constructor
         | [ H:False |- _]=> destruct H
         | [H: _ /\ _ |- _]=> destruct H
         | [H: _ \/ _ |-_]=>destruct H
         | [ H1:?P -> ?Q,H2: ?P|- _ ]=>specialize (H1 H2)
         end.

Section propsitional.
  Variables P Q R:Prop.
  Theorem propsitional:( P \/ Q \/ False)/\(P->Q)->True/\Q.
  Proof. my_tauto. Qed.
  Theorem m1 : True.
  Proof. match goal with
     | [|- _]=>intro
     | [|- True]=>constructor
     end. Qed.
End propsitional.
  Theorem m2 : forall P Q R:Prop, P->Q->R->Q.
    Proof. intros; match goal with
               | [H: _ |- _]=>exact H
               end. Qed.
    Ltac notHyp P:=
      match goal with
      | [_ : P |- _ ]=>fail 1
      | _ =>
        match P with
        | ?P1 /\ ?P2=>first [ notHyp P1| notHyp P2| fail 2]
        | _ =>idtac
        end
      end.
    Ltac extend pf:=
      let t:=type of pf in
      notHyp t; generalize pf; intro.
    Ltac completer:=
      repeat match goal with
             | [|-_ /\ _]=> constructor
             | [ H:_ /\ _ |- _]=>destruct H
             | [H:?P-> ?Q, H':?P|-_]=>specialize (H H')
             | [|-forall x, _]=>intro
             | [H:forall x,?P x-> _, H':?P ?X|-_]=>extend (H X H')
             end.
Section firstorder.
      Variable A : Set.
      Variables P Q R S:A->Prop.
      Hypothesis H1:forall x, P x->Q x /\ R x.
      Hypothesis H2:forall x,R x->S x.
      (* notes
      注意，一阶逻辑的命题 p->q 似乎被当作了全称命题forall p,q.
      所以，intro命令不但可以对全称命题引入，也可以对形如p->q
      的一阶命题引入
       *)
      Theorem fo : forall ( y x:A),P x->S x.
      Proof. completer. assumption. Qed.
End firstorder.

Ltac completer':=
  repeat match goal with
         | [|- _ /\ _]=>constructor
         | [H:?P /\ ?Q|-_]=>destruct H;
                          repeat match goal with
                                 | [H': P /\ Q|-_]=>clear H'
                                 end
         | [H:?P->_, H':?P|-_]=>specialize (H H')
         | [|- forall x,_]=>intro
         | [H:forall x,?P x->_ , H': ?P ?X |-_]=>extend (H X H')
         end.

Section firstorder'.
  Variable A : Set.
  Variables P Q R S:A->Prop.
  Hypothesis H1:forall x,P x->Q x /\ R x.
  Hypothesis H2:forall x,R x->S x.
  Theorem fo' : forall (y x:A), P x->S x.
    Proof. completer'. Abort. 
  Theorem t1 : forall x:nat, x=x.
    match goal with
    | [|-forall x, _]=>trivial
    end. Qed.
  Theorem t1' : forall x:nat, x=x.
    match goal with
    | [|-forall x, ?P]=>trivial
    end. Qed.
End firstorder'.
(* chap 14.3
Functional Programming iin Ltac
 *)
  Ltac length ls:=
    match ls with
    | nil=>O
    | _::?ls'=>constr:(S (length ls'))      
    end.
  Goal False.
  Abort.
  Reset length.
  
  Ltac length ls:=
    match ls with
    | nil=>O
    | _ :: ?ls'=>
      let ls'':=length ls' in
          constr:(S ls'')
    end.
  
  Goal False.
(*    let n:= length (1::2::3::nil) in pose n. *)
  Abort.
  
  Ltac map T f:=
    let rec map' ls:=
        match ls with
        | nil=>constr:(@nil T)
        | ?x::?ls'=>
          let x':= f x in
          let ls'':=map' ls' in
          constr:(x'::ls'')
        end in
    map'.

  Goal False.
    let ls:=map (nat*nat)%type ltac:(fun x=>constr:((x,x))) (1::2::3::nil) in pose ls.
  Abort.

  Reset length.
  Ltac length ls:=
    idtac ls;
    match ls with
    | nil=>O
    | _::?ls'=>
      let ls'':= length ls' in
      constr:(S ls'')
    end.

  Goal False.
    (*  let n:=length (1::2::3::nil) in pose n. *)
  Abort.

  Reset length.
  Ltac length ls k:=
    idtac ls;
    match ls with
    | nil => k O
    | _ :: ?ls'=>length ls' ltac:(fun n=>k (S n))
    end.
  Goal False.
    (* length (1::2::3::nil) ltac:(fun n=>pose n). *)
  Abort.

  (* 14.4 Recursion Proof Search *)

  Ltac inster n:=
    intuition;
    match n with   
    | S ?n'=>    
      match goal with  
      | [H:forall x:?T, _, y:?T|-_]=> generalize (H y); inster n'                                                 
      end
    end.

  Section test_inster.
    Variable A:Set.
    Variables P Q:A->Prop.
    Variable f : A->A.
    Variable g : A->A->A.
    Hypothesis H1:forall x y, P (g x y)->Q (f x).
    Theorem test_inster:forall x y,P (g x y)->Q (f x).
      inster 2. Qed.
  End test_inster.

  Definition imp (P1 P2:Prop) := P1->P2.
  Infix "->" := imp (no associativity, at level 91).
  Ltac imp:=unfold imp;firstorder.

  Theorem and_True_prem : forall P Q, (P /\ True->Q)->(P->Q).
    imp. Qed.
  Theorem and_True_conc:forall P Q, (P->Q /\ True)->(P->Q).
    imp. Qed.
  Theorem pick_prem1 : forall P Q R S, (P /\ (Q /\ R)->S)->((P /\ Q) /\ R->S).
    imp. Qed.
  Theorem pick_prem2 : forall P Q R S, (Q /\ (P /\ R)->S)->((P /\ Q) /\ R->S).
    imp. Qed.
  Theorem comm_prem : forall P Q R, (P /\ Q->R)->(Q /\ P->R).
    imp. Qed.
  Theorem pick_conc1 : forall P Q R S, (S->P/\(Q/\R))->(S->(P/\Q)/\R).
    imp. Qed.
  Theorem pick_conc2:forall P Q R S, (S->Q/\(P/\R))->(S->(P/\R)/\R).
    imp. Qed.
  Theorem comm_conc : forall P Q R, (R->P/\Q)->(R->Q/\P).
    imp. Qed.

  Ltac search_prem tac:=
    let rec search P:=
        tac
        || (apply and_True_prem; tac)
        || match P with
           | ?P1 /\ ?P2=>
             (apply pick_prem1; search P1)
             || (apply pick_prem2; search P2)
           end
        in match goal with
           | [|- ?P /\  _->_]=>search P
           | [|- _ /\ ?P->_]=>apply comm_prem; search P
           | [|- _->_]=>progress (tac || (apply and_True_prem; tac))
           end.

  Ltac search_conc tac:=
    let rec search P:=
        tac
        || (apply and_True_conc; tac)
        || match P with
           | ?P1 /\ ?P2=>
             (apply pick_conc1;search P1)
               || (apply pick_conc2; search P2)
           end
    in match goal with
       | [|-_-> ?P /\ _]=>search P
       | [|- _-> _/\ ?P]=>apply comm_conc;search P
       | [|-_->_]=>progress (tac || (apply and_True_conc; tac))
       end.

  Theorem False_prem:forall P Q, False /\ P->Q.
    imp. Qed.
  Theorem True_conc : forall P Q:Prop, (P->Q)->(P->True /\ Q).
    imp. Qed.
  Theorem Match : forall P Q R:Prop, (Q->R)->(P/\Q->P/\R).
    imp. Qed.
  Theorem ex_prem : forall (T:Type) (P:T->Prop) (Q R:Prop), (forall x,P x /\ Q->R)->(ex P /\Q->R).
    imp. Qed.
  Theorem ex_conc : forall (T:Type) (P:T->Prop) (Q R:Prop) x, (Q->P x /\ R)->(Q ->ex P /\ R).
    imp. Qed.
  Theorem imp_True : forall P,P->True.
    imp. Qed.

  Ltac matcher:=
    intros;
    repeat search_prem ltac:(simple apply False_prem || (simple apply ex_prem; intro));
    repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
                                                        || search_prem ltac:(simple apply Match));
    try simple apply imp_True.
  Theorem t2:forall P Q:Prop, Q /\ (P /\False)/\P->P/\Q.
    matcher. firstorder. Qed.
  Print t2.
  Theorem t3 : forall P Q R:Prop, P /\ Q ->Q /\ R /\P.
    matcher. Abort.
  Theorem t4:forall (P:nat->Prop) Q, (exists x, P x/\Q)->Q/\(exists x,P x).
    matcher. firstorder. Qed.
  Print t4.
  (* 14.5 Creating Unification Variables *)
  Theorem t5 : (forall x:nat, S x> x)->2>1.
    intros. evar (y : nat).
    let y':=eval unfold y in y in
        clear y;specialize (H y').
    apply H. Qed.
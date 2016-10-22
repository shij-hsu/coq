Theorem ex_mid_iff_d_neg: forall P:Prop, ~P\/P<->(P<->~~P).
Proof. intros. split.
       - intros. split. destruct H. intros. unfold not. intros. apply H1. apply H0.
         intros. unfold not. intros. apply H1. apply H. destruct H. unfold not in H.
         unfold not. intros. assert (False). { apply H0. apply H. } inversion H1.
         unfold not. intros. apply H.
       - unfold not. intros. destruct H.
               
                                       
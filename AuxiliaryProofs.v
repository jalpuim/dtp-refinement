Section AuxiliaryProofs.

Require Import Div2.
Require Import Even.
Require Import Plus.
Require Import Lt.

Theorem even_even_lt_div2 : forall m n, even m /\ even n -> m < n -> div2 m < div2 n.
Proof.
  intros m n.
  generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. inversion H2.
    intros m H1 H2. destruct H1. inversion H0. inversion H3.
    intros n' H1 m H2 H3. simpl. generalize dependent m. intros m.
    apply ind_0_1_SS with (n:=m). intros H2 H3. apply lt_O_Sn. intros H2 H3. apply lt_O_Sn.
    intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3. split. inversion H.
    inversion H5. trivial. inversion H0. inversion H5. trivial. 
    repeat apply lt_S_n in H4. exact H4.
Qed.

Theorem even_plus_div2 : forall m n,
  even m -> div2 (m + n) = div2 m + div2 n.
Proof.
  intros m n.
  apply ind_0_1_SS with (n:=m).
    intros H. simpl. reflexivity.
    intros H. inversion H. inversion H1.
    intros x Hind H1. simpl. apply eq_S. apply Hind. inversion H1. inversion H0. trivial.
Qed.

Theorem even_odd_lt_div2 : forall m n, 
  even m /\ odd n -> Datatypes.S m < n -> div2 m < div2 n.
Proof.
  intros m n. generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. destruct H1 as [H3 H4]. inversion H4.
    intros m H1 H2. simpl. inversion H2. subst. inversion H0.
    intros n' H1 m H2 H3. simpl. generalize dependent m. intros m.
    apply ind_0_1_SS with (n:=m). intros H2 H3. simpl. apply lt_O_Sn.
    intros H2 H3. simpl. apply lt_O_Sn.
    intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H5 H6]. split. 
    inversion H5. inversion H0. trivial. inversion H6. inversion H0. trivial.
    repeat apply lt_S_n in H4. exact H4.
Qed.

Theorem odd_even_lt_div2 : forall m n,
  odd m /\ even n -> Datatypes.S m < n -> Datatypes.S (div2 m) < div2 n.
Proof.
  intros m.
  apply ind_0_1_SS with (n:=m). 
      intros n H1 H2. destruct H1 as [H1 H3]. inversion H1.
      intros n H1 H2. simpl. inversion H2. destruct H1 as [H1 H3]. rewrite <- H in H3.
      inversion H3. inversion H4. inversion H6. inversion H8.
      subst. destruct H1 as [H1 H3]. inversion H1. subst. inversion H. simpl. auto.
      subst. simpl. apply lt_n_S. inversion H0. simpl. auto. subst. inversion H5. simpl.
      auto. simpl. apply lt_O_Sn.
      intros n' H1 n H2 H3. simpl.
      generalize dependent n. intros n.
      apply ind_0_1_SS with (n:=n). intros H2 H3. inversion H3.
      intros H2 H3. inversion H3. inversion H0.
      intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H3 H5].
      split. inversion H3. inversion H0. trivial. inversion H5. inversion H0. trivial.
      repeat apply lt_S_n in H4. trivial.
Qed.     

Theorem odd_odd_plus_div2 : forall m n,
  odd m /\ odd n -> div2 (m + n) = Datatypes.S (div2 m + div2 n).
Proof.
  intros m n.
  apply ind_0_1_SS with (n:=m).
    intros H1. destruct H1 as [H1 H2]. inversion H1.
    apply ind_0_1_SS with (n:=n).
      intros H1. destruct H1 as [H1 H2]. inversion H2.
      intros H1. simpl. reflexivity.
      intros n' H1 H2. rewrite plus_comm. simpl. apply eq_S. rewrite plus_comm.
      apply H1. destruct H2 as [H2 H3]. split. trivial. inversion H3. inversion H0. trivial.
    intros x Hind H1. simpl. apply eq_S. apply Hind. destruct H1 as [H1 H2]. split.
    inversion H1. inversion H0. trivial. trivial.
Qed.

Theorem odd_odd_lt_div2 : forall m n,
  odd m /\ odd n -> m < n -> div2 m < div2 n.
Proof.
  intros m n. generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. inversion H2.
    intros m H1 H2. inversion H2. rewrite H0 in H1. destruct H1 as [H1 H3]. inversion H1.
    inversion H0.
    intros n' H1 m. apply ind_0_1_SS with (n:=m).
      intros H2 H3. destruct H2 as [H4 H5]. inversion H4.
      intros H2 H3. simpl. inversion H3. destruct H2 as [H2 H4]. 
      rewrite <- H0 in H4. inversion H4. inversion H5. inversion H7. apply lt_O_Sn.
      intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H3 H5].
      split. inversion H3. inversion H0. trivial. inversion H5. inversion H0. trivial.
      repeat apply lt_S_n in H4. exact H4.
Qed.

End AuxiliaryProofs.
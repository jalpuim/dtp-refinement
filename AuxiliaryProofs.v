Section AuxiliaryProofs.

Require Import Div2.
Require Import Even.
Require Import Plus.
Require Import Lt.
Require Import Mult.
Require Import Omega.

(* Even/Odd proofs *) 

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

(* Prop proofs *)

Lemma or_imp_l : forall (p q s : Prop),
  p \/ q ->
  (p -> s) ->
  s \/ q.
Proof.
  intros p q s H1 H2.
  inversion H1 as [H | H].
  apply H2 in H.
  left; assumption.
  right; assumption.
Qed.

Lemma or_imp_r : forall (p q t : Prop),
  p \/ q ->
  (q -> t) ->
  p \/ t.
Proof.
  intros p q t H1 H2.
  inversion H1 as [H | H].
  left; assumption.
  apply H2 in H.
  right; assumption.
Qed.

Lemma or_imp : forall (p q t s : Prop),
  p \/ q ->
  (p -> s) ->
  (q -> t) ->
  s \/ t.
Proof.
  intros p q t s H1 H2 H3.
  inversion H1 as [H | H].
  apply H2 in H.
  left; assumption.
  apply H3 in H.
  right; assumption.
Qed.

(* Lt proofs *)

Lemma lt_n_sq : forall (m n : nat), m < n -> m * m < n * n.
Proof.
  intros.
  destruct m.
  destruct n.
  inversion H.
  simpl; apply lt_0_Sn.
  assert (H': Datatypes.S m < n) by (apply H).
  apply mult_lt_compat_l with (p:=n) in H.
  apply lt_trans with (m:= (n * Datatypes.S m)).
  apply mult_lt_compat_r with (p:= Datatypes.S m) in H'.
  assumption.
  apply lt_0_Sn.
  assumption.
  inversion H; apply lt_0_Sn.
Qed.

Lemma lt_plus_compat_l : forall m n p,
  p + m < p + n ->
  m < n.
Proof.
  intros.
  induction p.
  simpl in H.
  apply H.
  simpl in H.
  apply lt_S_n in H.
  apply IHp.
  apply H.
Qed.

Lemma lt_mult_compat_l : forall m n p,
  p * m < p * n ->
  m < n. 
Proof.
  intros m.
  induction m.
  destruct n.
  intros; rewrite mult_comm in H; inversion H.
  intros; apply lt_0_Sn.
  intros.
  destruct p.
  simpl in H; inversion H.
  destruct n.
  replace (Datatypes.S p * 0) with (0 * Datatypes.S p) in H by (apply mult_comm).
  simpl in H; inversion H.
  rewrite mult_comm in H. 
  replace (Datatypes.S p * Datatypes.S n) with (Datatypes.S n * Datatypes.S p) in H
          by (apply mult_comm).  
  simpl in H.
  apply lt_S_n in H.
  apply lt_plus_compat_l in H.
  rewrite mult_comm in H.
  replace (n * Datatypes.S p) with (Datatypes.S p * n) in H by (apply mult_comm).
  apply IHm in H.
  apply lt_n_S.
  assumption.
Qed.

Lemma lt_plus_or : forall (q n m p : nat), 
  p + m < q + n -> 
  p < q \/ m < n.
Proof.
  intros q.
  induction q.
  intros n.
  induction n.
  intros.
  inversion H.
  simpl in *.
  destruct p.
  simpl.
  right; assumption.
  intros.
  destruct m.
  simpl in *.
  apply lt_S_n in H.
  apply or_imp with (p := p < 0) (q := 0 < n).
  apply IHn.
  assumption.
  intros contra; inversion contra.
  intros; apply lt_0_Sn.
  rewrite plus_comm in H.
  simpl in H.
  apply lt_S_n in H.
  rewrite plus_comm in H.
  apply or_imp_r with (q := m < n).
  apply IHn; assumption.
  intros; apply lt_n_S; assumption.

  intros.
  destruct p.
  left; apply lt_0_Sn.
  apply or_imp_l with (p := p < q).
  apply IHq.
  simpl in H.
  apply lt_S_n in H.
  assumption.
  intros; apply lt_n_S; assumption.
Qed.
  
Lemma lt_plus_n : forall m n, m + m < n + n -> m < n.
Proof.
  intros m n.
  generalize dependent m.
  induction n.
  intros.
  destruct m.
  inversion H.
  simpl in *; inversion H.
  intros.
  destruct m.
  apply lt_0_Sn.
  apply lt_n_S.
  apply IHn.
  simpl in H; apply lt_S_n in H.
  rewrite plus_comm in H.
  replace (n + Datatypes.S n) with (Datatypes.S n + n) in H by (apply plus_comm).
  simpl in H; apply lt_S_n in H.
  assumption.
Qed.

Lemma lt_sq_n : forall (m n : nat), m * m < n * n -> m < n.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m Hm].
  intros.
  destruct n.
  inversion H.
  apply lt_0_Sn.
  intros.
  destruct n.
  inversion H.
  simpl in *.
  apply lt_S_n in H.
  apply lt_n_S.
  rewrite plus_comm in H; rewrite mult_comm in H.
  simpl in H.
  replace (n + n * Datatypes.S n) with (Datatypes.S n * n + n) in * by
          (rewrite plus_comm; rewrite mult_comm; reflexivity).
  simpl in *.
  replace (m + m * m + m) with (m + m + m * m) in H by omega.
  replace (n + n * n + n) with (n + n + n * n) in H by omega.
  apply lt_plus_or with (p := m + m) (q := n + n) in H.
  inversion H as [H1 | H1].
  apply lt_plus_n in H1.
  assumption.
  apply Hm.
  assumption.
Qed.

End AuxiliaryProofs.
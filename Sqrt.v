Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Div2.
Require Import While.
Require Import Heap.
Require Import Refinement.
Require Import Program.Tactics.
Require Import Program.Equality.

Definition square : nat -> nat := fun n => n * n.

Definition sqrtSpec (ptr : Ptr) : WhileL nat nat.
  refine (Spec _).
  refine (Predicate (fun s => {x : nat | find s ptr = Some x}) _).
  intros s [x H] result s'.
  apply (square result <= x < square (result+1)).
Defined.

Definition find_eqb_some (h : option nat) : nat :=
  match h with
    | Some n => n
    | _ => 0
  end.

Definition Inv (Q R : Ptr) (s : nat) (si st : heap nat) :=
  { q : nat & prod (find st Q = Some q) (
  { r : nat & prod (find st R = Some r) (
            prod (le (square r) s) (
            prod (lt s (square q))
                 (R <> Q))) } ) }.

Definition Cond (Q R : Ptr) (st : heap nat) :=
  negb (Nat.eqb (find_eqb_some (find st R) + 1)
                (find_eqb_some (find st Q))).

Lemma ifSpec {a v} (cond : bool) (spec : PT v a) (wt we : WhileL v a) :
  (if cond then Spec spec ⊑ wt else Spec spec ⊑ we) ->
  (Spec spec ⊑ (if cond then wt else we)).
Proof. destruct cond; intros; assumption. Qed.

Hint Unfold isExecutable square.
Hint Resolve Nat.ltb_lt Lt.lt_n_Sm_le.
Hint Resolve le_0_n leb_iff_conv beq_nat_eq.

Ltac WHILE I c := apply (whileSpec I c); goal_simpl.
Ltac ITE c := apply (ifSpec c); remember c as b; destruct b; goal_simpl.

(*** Derivation ***)

Definition sqrtResult (ptr : Ptr) :
  { c : WhileL nat nat & prod (sqrtSpec ptr ⊑ c) (isExecutable c) }.
Proof.
  econstructor; unfold sqrtSpec. split.
  - READ ptr s.
    NEW (s + 1) Q.
    NEW 0 R.
    WHILE (Inv Q R s) (Cond Q R); unfold Inv, Cond.
    * repeat (eexists; split; eauto); repeat split; eauto.
      rewrite Nat.add_comm; apply Nat.lt_lt_add_r; auto.
    * READ Q vInQ.
      READ R vInR.
      ITE (s <? square (Nat.div2 (vInQ + vInR))).
      WRITE Q (Nat.div2 (vInQ + vInR)).
      RETURN tt.
      repeat (eexists; split; eauto); repeat split; eauto.   
      now apply Nat.ltb_lt.
      WRITE R (Nat.div2 (vInQ + vInR)).
      eapply (@writeSpec _ _ R (Nat.div2 (vInQ + vInR))); goal_simpl.
      RETURN tt.
      repeat (eexists; split; eauto); repeat split; eauto.
      symmetry in Heqb; apply Lt.lt_n_Sm_le; now apply leb_iff_conv. 
    * READ R vInR.
      RETURN vInR.
      auto.
      rewrite e1 in i; rewrite e0 in i; simpl in i.
      remember (vInR + 1 =? s3) as b; destruct b. 
      apply beq_nat_eq in Heqb; now subst.
      exfalso; now simpl in i.
  - repeat (simpl; intros; split; intros);
    destruct (v <? square (Nat.div2 (v0 + v1))); auto.
Defined.

Variable t : Ptr.

Eval simpl in projT1 (sqrtResult t).

(*** Verification ***)

Definition sqrt (ptr : Ptr) : WhileL nat nat.
refine (
  Read ptr (fun s =>
  New (s + 1) (fun Q =>
  New 0 (fun R =>
  While (Inv Q R s)
        (Cond Q R)
        (Read Q (fun vInQ =>
        (Read R (fun vInR =>
        let p := div2 (vInQ + vInR)
        in if (s <? square p)
           then Write Q p (Return _ tt)
           else Write R p (Return _ tt)))))
  (Read R (fun vInR => Return _ vInR)))))).
Defined.

Lemma sqrtRefinement : forall ptr, wrefines (sqrtSpec ptr) (sqrt ptr).
Proof.
  intro ptr; unfold sqrtSpec.
  READ ptr s.
  NEW (s + 1) Q.
  NEW 0 R.
  unfold Inv, Cond; apply whileSpec.
  - refine_simpl.
    unfold lift_opt_prop, square; simpl; rewrite findUpdate; simpl; apply le_0_n.
    unfold square; simpl; rewrite findNUpdate.
    unfold Nat.lt; rewrite findUpdate; simpl.
    remember ((s + 1) * (s + 1)).
    rewrite Nat.add_comm in Heqn1 at 1; simpl in Heqn1.
    rewrite Nat.add_comm with (m := 1) in Heqn1; rewrite Heqn1.
    apply Nat.le_add_r.
    unfold not; intro H'; subst.
    assert (Ha : R <> R) by eauto; now apply Ha.
    unfold not; intro H'; subst.
    assert (Ha : Q <> Q) by eauto; now apply Ha.
  - READ Q vInQ.
    remember (find s0 Q).
    destruct o; [ eauto | exfalso; assumption ].
    READ R vInR.
    unfold lift_opt_prop in l.
    remember (find s0 R) as r; destruct r; [ eauto | exfalso; assumption ].
    remember (s <? square (Nat.div2 (vInQ + vInR))) as b.
    destruct b.
    WRITE Q (Nat.div2 (vInQ + vInR)).
    RETURN tt;
    try rewrite findUpdate; try rewrite findNUpdate; auto.
    rewrite e1 in y; rewrite e0 in l; symmetry in Heqb; now apply Nat.ltb_lt.
    WRITE R (Nat.div2 (vInQ + vInR)).
    RETURN tt;
    try rewrite findUpdate; try rewrite findNUpdate; auto.
    simpl; symmetry in Heqb; apply leb_iff_conv in Heqb;
    now apply Lt.lt_n_Sm_le in Heqb.
  - READ R vInR.
    unfold lift_opt_prop in l.
    remember (find s0 R) as r; destruct r; [ eauto | exfalso; assumption ].
    RETURN vInR.
    * rewrite e in l; simpl in l; auto.
    * rewrite e in i; simpl in i.
      remember (find s0 Q) as q; destruct q.
      remember (vInR + 1 =? n2) as b; destruct b.
      apply beq_nat_eq in Heqb.
      now subst.
      exfalso; simpl in i; rewrite <- Heqb in i; auto.
      exfalso; assumption.
Qed.

(* Refinement with Type *)

Definition lift_opt {a b} (f : a -> a -> b) (v1 : option a) (v2 : option a) : option b :=
  match v1,v2 with
    | Some x, Some y => Some (f x y)
    | _, _ => None
  end.

Definition sqrt_type (ptr : Ptr) : WhileL nat nat.
refine (
  Read ptr (fun s =>
  New (s + 1) (fun Q =>
  New 0 (fun R =>
  While (fun _ st =>
    prod (lift_opt (fun r s => Nat.leb (square r) s) (find st R) (Some s) = Some true)
    (prod (lift_opt (fun s q => Nat.ltb s (square q)) (Some s) (find st Q) = Some true) (R <> Q)))
        (fun st => negb (Nat.eqb (find_eqb_some (find st R) + 1)
                                 (find_eqb_some (find st Q)))) 
        (Read Q (fun vInQ =>
        (Read R (fun vInR =>
        let p := div2 (vInQ + vInR)
        in if (s <? square p)
           then Write Q p (Return _ tt)
           else Write R p (Return _ tt)))))
  (Read R (fun vInR => Return _ vInR)))))).
Defined.

Lemma sqrtRefinement_type : forall ptr, wrefines (sqrtSpec ptr) (sqrt_type ptr).
Proof.
  intro ptr; unfold sqrtSpec.
  READ ptr s.
  NEW (s + 1) Q.
  NEW 0 R.
  apply whileSpec.
  - refine_simpl.
    unfold lift_opt, square; simpl; rewrite findUpdate; now simpl.
    unfold lift_opt, square; simpl. rewrite findNUpdate.
    unfold Nat.ltb; rewrite findUpdate; simpl.
    remember ((s + 1) * (s + 1)).
    rewrite Nat.add_comm in Heqn1. simpl in *.
    rewrite Heqn1.
    apply f_equal; apply Nat.leb_le.
    apply Nat.le_add_r.
    unfold not; intro H'; subst.
    assert (Ha : R <> R) by eauto; now apply Ha.
    unfold not; intro H'; subst.
    assert (Ha : Q <> Q) by eauto; now apply Ha.
  - READ Q vInQ.
    remember (find s0 Q). destruct o. eauto. inversion e0.
    READ R vInR.
    unfold lift_opt in e0.
    remember (find s0 R). destruct o. eauto. inversion e0.
    remember (s <? square (Nat.div2 (vInQ + vInR))).
    destruct b.
    WRITE Q (Nat.div2 (vInQ + vInR)).
    RETURN tt.
    rewrite findNUpdate; auto.
    rewrite findUpdate; apply f_equal.
    rewrite e0 in e2; rewrite e1 in e3.
    now rewrite <- Heqb.
    auto.
    WRITE R (Nat.div2 (vInQ + vInR)).
    RETURN tt.
    rewrite findUpdate; auto.
    simpl; apply f_equal.
    symmetry in Heqb.
    apply leb_iff_conv in Heqb.
    apply Lt.lt_n_Sm_le in Heqb.
    now apply Nat.leb_le.
    rewrite findNUpdate; auto.
    auto.
  - READ R vInR.
    unfold lift_opt in e.
    remember (find s0 R) as r; destruct r. eauto. inversion e.
    RETURN vInR.
    * rewrite e in e0; simpl in e0.
      inversion e0.  now apply leb_complete in H1.
    * rewrite e in i.
      remember (find s0 Q) as q.
      destruct q; inversion e1. unfold "<?" in H1. unfold lt.
      apply leb_complete in H1.
      simpl in i.
      remember (vInR + 1 =? n2).
      destruct b.
      apply beq_nat_eq in Heqb.
      now subst.
      exfalso; now simpl in i.
Qed.

    
  
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

(************************************************************

                      SQUARE ROOT EXAMPLE

*************************************************************)

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

Hint Unfold isExecutable square.
Hint Resolve Nat.ltb_lt Lt.lt_n_Sm_le.
Hint Resolve le_0_n leb_iff_conv beq_nat_eq.

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

    
  
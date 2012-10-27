Require Import Div2.
Require Import Even.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import AuxiliaryProofs.
Require Import Bool.
Require Import While.
Import While.Language.
Import While.Semantics.

Module Test.
Import While.CodeGeneration.
Import Bool.

Lemma step {SPEC} (R : WhileL) :
  SPEC ⊑ R ->
  (exists C, ((R ⊑ C) /\ isExecutable C)) ->
  exists C, ((SPEC ⊑ C) /\ isExecutable C).
Proof.
  intros H1 H2.
  inversion H2 as [w [H3 H4]].
  exists w.
  split; try apply (refineTrans R); assumption.
Qed.

Definition SWAP := Spec ([fun _ => True, fun s _ s' => varP s = varQ s' /\ varP s' = varQ s]).

Definition SwapAssign := 
  Spec (Assign_PT (fun s => mkS (varN s) (varQ s) (varP s) (varR s))).

Definition swapResult :
  SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N).
Proof.
  apply (refineTrans
          (Spec ([fun _ => True , fun s _ s' => varP s = varQ s' /\ varN s' = varQ s]) ; 
           P ::= Var N)).
  apply refineFollowAssign.
  destruct s as [N P Q R]; destruct s' as [N' P' Q' R']; simpl; intros; assumption.
  apply refineSeqAssocR.
  apply refineSplit; try apply refineRefl.
  apply (refineTrans
          (Spec ([fun _ => True , fun s _ s' => varP s = varP s' /\ varN s' = varQ s]) ;
            Q ::= Var P)).
  apply refineFollowAssign.
  destruct s as [N P Q R]; destruct s' as [N' P' Q' R']; simpl; intros; assumption.
  apply refineSplit; try apply refineRefl.
  apply refineAssign.
  simpl; intros.
  destruct s as [N P Q R]; simpl.
  split; reflexivity.
Defined.

Lemma foo : 
  exists c, ((SWAP ⊑ c) /\ isExecutable c).
Proof.
  apply (step (N ::= Var P)).  
  apply refineAssign.
  unfold semantics.
  simpl.
  intros.
  destruct s.
  simpl.
Admitted.

End Test.

Module Definitions.

Definition square : nat -> nat := fun n => n * n.

Definition Inv : S -> Prop := fun X => square (varR X) <= varN X < square (varQ X).

Definition WSPEC := Spec ([ (fun _ => True), fun _ _ X => square (varR X) <= varN X < square (1 + varR X)]).

Definition W1 := Spec ([ fun _ => True, fun _ _ X => Inv X /\ 1 + varR X = varQ X]).

Definition W2 := (Spec ([fun _ => True , K Inv])) ; (Spec ([Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X])).

Definition PT3a :=
  Assign_PT (fun s => mkS (varN s) (varP s) (1 + (varN s)) 0).

Definition W3aa :=
  R ::= (EConst 0).

Definition W3ab :=
  Q ::= (Plus (EConst 1) (Var N)).

Definition W3a := W3aa ; W3ab.

Definition WBody := 
  Spec ([(fun s => Inv s /\ Is_true (negb (beq_nat (1 + varR s) (varQ s)))),
          (fun _ _ s' => Inv s')]).  

Definition W3b :=
  let guard := (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) in
  While Inv guard WBody.

Definition W4 :=
  (Spec ([fun X => 1 + varR X < varQ X /\ Inv X, 
          fun _ _ X => varR X < varP X < varQ X /\ Inv X])) ;
  (Spec ([fun X => varR X < varP X < varQ X /\ Inv X, fun _ _ X => Inv X])).

Definition W5a :=
  P ::= (Div2 (Plus (Var Q) (Var R))).

Definition W5bThen := 
  Spec ([fun s => (varN s < square (varP s)) /\ (varP s < varQ s) /\ Inv s,
         fun _ _ s' => Inv s']).

Definition W5bElse := 
  Spec ([fun s => (varN s >= square (varP s)) /\ (varR s < varP s) /\ Inv s,
         fun _ _ s' => Inv s']).

Definition W5b :=
  If (Lt (Var N) (Mult (Var P) (Var P))) W5bThen W5bElse.

End Definitions.

Module Proof.

Import Definitions.
Import While.CodeGeneration.
Import Bool.

Ltac refine_post_pt pt1 pt2 := apply (Refinement _ _ (fun s (y : pre pt1 s) => y : pre pt2 s)). 

Ltac refine_post w1 w2 := 
  apply (Refinement _ _ (fun s (y : pre (semantics w1) s) => y : pre (semantics w2) s)).

Ltac assert_pre w1 w2 := 
  assert (d : pre (semantics w1) ⊂ pre (semantics w2));
  unfold pre,subset,semantics,w1,w2.

Lemma step1 : WSPEC ⊑ W1.
  Proof.    
    refine_post WSPEC W1.
    unfold subset.
    intros X tt s [H1 H2]; simpl in *; rewrite H2; apply H1.  
  Qed.

Lemma step2 : W1 ⊑ W2.
  Proof.
    assert_pre W1 W2.
    intros; exists I; intros; auto.
    apply (Refinement _ _ d).
    simpl; intros s Pre s' [t [H1 [H2 H3]]]; split; auto.
Qed.

Lemma step3 : W2 ⊑ W3a ; W3b.
Proof.
  unfold W2,W3a,W3aa,W3ab,W3b,"⊑",semantics.
  apply refineSplitPT.
  simpl.
  unfold Assign_PT, K, Inv.
  apply (refineTransPT PT3a).
  (* Part a *)
    unfold K, Inv, PT3a, square; apply refineAssignPT.
    simpl; intros; split; auto with arith.
  (* refineTrans *)
  unfold PT3a,Assign_PT.
  apply refineSeqAssignPT.
  intros; destruct s; simpl; reflexivity.
  (* Part b *)
     unfold WBody,evalBExpr,evalExpr.
     apply refineWhile.
     intros.
     destruct s as [N P Q R]; simpl in *.
     destruct Q as [|Q].
     inversion H.
     case_eq (beq_nat R Q); intros H'.
     symmetry in H'; apply beq_nat_eq in H'.
     rewrite H'; reflexivity.
     rewrite H' in H; inversion H.
  Qed.
  
Lemma step4 : WBody ⊑ W4.
  assert_pre WBody W4.
  simpl; intros.
  split. 
  inversion H as [H1 H2]; inversion H1 as [H3 H4].
  split. 
  unfold square in *; destruct s as [N P Q R]; unfold Inv in *; simpl in *.
  unfold Is_true,negb in H2.
  remember (if match Q with
             | 0 => false
             | Datatypes.S m1 => beq_nat R m1
             end
          then false
          else true) as e.
  destruct e; induction Q as [|Q HQ]. 
  unfold square in H4; simpl in H; inversion H4.
  remember (beq_nat R Q) as beq; destruct beq; inversion Heqe. 
  symmetry in Heqbeq; apply beq_nat_false in Heqbeq.
  unfold not in Heqbeq; clear H2; clear Heqe.
  unfold square in *.
  apply le_lt_trans with (p:=Datatypes.S Q * Datatypes.S Q) in H3.
  apply lt_sq_n in H3; unfold "<" in H3; inversion H3. 
  exfalso; apply Heqbeq; assumption.
  subst; unfold "<"; apply le_n_S; assumption.
  assumption.
  exfalso; assumption.
  exfalso; assumption.
  assumption.
  intros s' [H1 H2]; inversion H as [H3 H4]; split; assumption.

  apply (Refinement _ _ d).
  intros s PreS; unfold post,subset in *; simpl in *.
  intros; inversion H as [x [H1 x']]; assumption.
Qed.

Lemma step5 : W4 ⊑ W5a ; W5b.
  apply refineSplit.
  simpl.
  apply refineAssign.
  simpl.
  intros s H.
  split.
  destruct s as [N P Q R].
  unfold Inv in H.
  simpl in *.
  split.  
  inversion H as [H1 H2].

  (** even-odd approach **)
  assert (Ha: even R \/ odd R).
  apply even_or_odd. destruct Ha as [Reven|Rodd].

  (* varR0 even *)
  assert (Ha: even Q \/ odd Q). apply even_or_odd. destruct Ha as [Qeven|Qodd].

  (* varR0 even, varQ0 even *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O.
  rewrite even_plus_div2. rewrite even_plus_div2. apply plus_lt_compat_r.
  apply even_even_lt_div2. split; trivial. apply le_Sn_le in H1. exact H1. trivial. trivial.

  (* varR0 even, varQ0 odd *)
  rewrite plus_comm. rewrite even_plus_div2. rewrite plus_comm. 
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  apply plus_lt_compat_r. apply even_odd_lt_div2. split; trivial. trivial. trivial. trivial.

  (* varR0 odd *)
  assert (Ha: even Q \/ odd Q). apply even_or_odd. destruct Ha as [Qeven|Qodd].
  
  (* varR0 odd, varQ0 even *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite even_plus_div2. rewrite <- plus_Sn_m. apply plus_lt_compat_r. 
  apply odd_even_lt_div2. split; trivial. trivial. trivial. split; trivial.

  (* varR0 odd, varQ0 odd *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite odd_odd_plus_div2. apply lt_n_S. apply plus_lt_compat_r. apply odd_odd_lt_div2. 
  split; trivial. apply le_Sn_le in H1. trivial. split; trivial. split; trivial.
  (** end goal **)

  inversion H as [H1 H2].

  (** even-odd approach **)
  assert (Ha: even R \/ odd R). apply even_or_odd. destruct Ha as [Reven|Rodd].
  (* varR0 even *)
  assert (Ha: even Q \/ odd Q). apply even_or_odd. destruct Ha as [Qeven|Qodd].
  
  (* varR0 even, varQ0 even *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  rewrite even_plus_div2. rewrite plus_comm. apply plus_lt_compat_r. 
  apply even_even_lt_div2. split; trivial. apply le_Sn_le in H1. exact H1. trivial. trivial.

  (* varR0 even, varQ0 odd *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite plus_comm. 
  rewrite even_plus_div2. rewrite odd_odd_plus_div2. rewrite <- plus_Sn_m. 
  apply plus_lt_compat_r. apply lt_S. apply even_odd_lt_div2. split; trivial. trivial. 
  split; trivial. trivial.

  (* varR0 odd *)
  assert (Ha: even Q \/ odd Q). apply even_or_odd. destruct Ha as [Qeven|Qodd].
  
  (* varR0 odd, varQ0 even *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  rewrite even_plus_div2. rewrite plus_comm. apply plus_lt_compat_r. apply le_Sn_le. 
  apply odd_even_lt_div2. split; trivial. trivial. trivial. trivial.

  (* varR0 odd, varQ0 odd *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite odd_odd_plus_div2. apply lt_n_S. rewrite plus_comm. apply plus_lt_compat_r. 
  apply odd_odd_lt_div2. split; trivial. apply le_Sn_le in H1. trivial. split; trivial. 
  split; trivial.
  (** end goal **)

  inversion H as [H1 [H2 H3]].
  unfold Inv in *.
  split; destruct s as [N P Q R]; simpl in *; assumption.  
  unfold Inv,W5b.
  unfold "⊑",semantics,W5bThen,W5bElse.
  assert (d: pre ([fun X : S => varR X < varP X < varQ X /\ square (varR X) <= varN X < square (varQ X),
             fun (s : S) (_ : varR s < varP s < varQ s /\ square (varR s) <= varN s < square (varQ s)) 
             (X : S) => square (varR X) <= varN X < square (varQ X)])
             ⊂ pre (semantics W5b)).
  unfold pre,semantics,subset,W5b; simpl.
  intros s [[H1 H2] [H3 H4]].
  destruct s as [N P Q R]; simpl in *.
  unfold Inv,Is_true,Is_false; simpl.
  remember (proj1_sig (nat_lt_ge_bool N (P * P))) as e; destruct e.
  unfold proj1_sig,nat_lt_ge_bool,Sumbool.bool_of_sumbool,sumbool_rec in *.
  unfold sumbool_rect,Sumbool.sumbool_not in *.
  remember (lt_ge_dec N (P * P)) as e; destruct e.
  split; intros H5.
  repeat split; assumption.
  inversion H5.
  inversion Heqe.
  unfold proj1_sig,nat_lt_ge_bool,Sumbool.bool_of_sumbool,sumbool_rec in *.
  unfold sumbool_rect,Sumbool.sumbool_not in *.
  remember (lt_ge_dec N (P * P)) as e; destruct e.
  inversion Heqe.
  split; intros H5.
  inversion H5.
  repeat split; assumption.

  apply (Refinement _ _ d).
  simpl; unfold subset; intros s PreS s' H.
  inversion PreS as [H1 H2].
  assert (Ha: forall b, or (Is_true b) (Is_false b)) by 
         (intros; destruct b; simpl in *; auto). 
  destruct s as [N P Q R]; simpl in *.
  inversion H as [H3 H4]. 
  assert (H': or (Is_true (proj1_sig (nat_lt_ge_bool N (P * P))))
                 (Is_false (proj1_sig (nat_lt_ge_bool N (P * P))))) by (apply Ha).
  inversion H' as [H5 | H5].
  apply H3 in H5; assumption.
  apply H4 in H5; assumption.
Qed.

Lemma step6Then : W5bThen ⊑ Q ::= (Var P).
Proof.
  apply refineAssign.
  simpl.
  intros s H.
  unfold Inv in *.
  destruct H as [H1 [H2 [H3 H4]]].
  destruct s as [N P Q R].
  simpl in *.
  split.
  assumption.
  assumption.
Qed.

Lemma step6Else : W5bElse ⊑ R ::= (Var P).
Proof.
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 [H2 [H3 H4]]].
  destruct s. unfold Inv in *.
  simpl in *.
  split; auto.
Qed.

Definition prgrm := (R ::= (EConst 0) ; Q ::= (Plus (EConst 1) (Var N))) ;
  (While Inv (Not (Eq (Plus (EConst 1) (Var R)) (Var Q)))
         (P ::= (Div2 (Plus (Var Q) (Var R))) ; (If (Lt (Var N) (Mult (Var P) (Var P))) 
                      (Q ::= (Var P)) 
                      (R ::= (Var P))))).

Theorem result : WSPEC ⊑ prgrm.
Proof.
  apply (refineTrans W1); try apply step1.
  apply (refineTrans W2); try apply step2.
  apply (refineTrans (W3a ; W3b)); try apply step3.
  apply refineSplit; try apply refineRefl.
  unfold W3b; apply refineBody.
  apply (refineTrans W4); try apply step4.
  apply (refineTrans (W5a ; W5b)); try apply step5.
  apply refineSplit; try apply refineRefl.
  unfold W5b; apply refineSplitIf; [apply step6Then | apply step6Else]. 
Qed.

Lemma prgrmProof : isExecutable prgrm.
Proof.  
  unfold prgrm,isExecutable; simpl; auto.
Qed.

Require Import String.
Compute (whileToCode prgrm prgrmProof).

(*
Extraction Language Haskell.
Extraction "Example.hs" prgrm.
*)


End Proof.


Module Example.

Require Import Div2.
Require Import Even.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import AuxiliaryProofs.

Load While.
Import While.

Module Definitions.

Import While.Language.
Require Import Bool.

Definition square : nat -> nat := fun n => n * n.

Definition Inv : S -> Prop := fun X => square (varR X) <= varN X < square (varQ X).

Definition SPEC := 
  ([ (fun _ => True), fun _ _ X => square (varR X) <= varN X < square (1 + varR X)]).

Definition WSPEC := Spec SPEC.

Definition PT1 :=
  ([ fun _ => True, fun _ _ X => Inv X /\ 1 + varR X = varQ X]).

Definition WPT1 := Spec PT1.

Definition PT2 := [fun _ => True , K Inv] ;; 
                  [Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X].

Definition WPT2 := (Spec ([fun _ => True , K Inv])) ; (Spec ([Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X])).

Definition PT3a :=
  Assign_PT (fun s => mkS (varN s) (varP s) (1 + (varN s)) 0).

Definition WPT3aa :=
  R ::= (EConst 0).

Definition WPT3ab :=
  Q ::= (Plus (EConst 1) (Var N)).

Definition WPT3a := WPT3aa ; WPT3ab.

Definition PT3b :=
  While_PT Inv (fun X => negb (beq_nat (1 + varR X) (varQ X)))
        ([(fun s => Inv s /\ Is_true (negb (beq_nat (1 + varR s) (varQ s)))),
          (fun _ _ s' => Inv s')]).

Definition WBody := 
  Spec ([(fun s => Inv s /\ Is_true (negb (beq_nat (1 + varR s) (varQ s)))),
          (fun _ _ s' => Inv s')]).  

Definition WPT3b :=
  let guard := (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) in
  While Inv guard WBody.

Definition WPT4 :=
  (Spec ([fun X => 1 + varR X < varQ X /\ Inv X, 
          fun _ _ X => varR X < varP X < varQ X /\ Inv X])) ;
  (Spec ([fun X => varR X < varP X < varQ X /\ Inv X, fun _ _ X => Inv X])).

Definition WPT5a :=
  P ::= (Div2 (Plus (Var Q) (Var R))).

Definition PT5bThen := 
  [fun s => (varN s < square (varP s)) /\ (varP s < varQ s) /\ Inv s,
   fun _ _ s' => Inv s'].

Definition WPT5bThen := 
  Spec ([fun s => (varN s < square (varP s)) /\ (varP s < varQ s) /\ Inv s,
         fun _ _ s' => Inv s']).

Definition WPT5bElse := 
  Spec ([fun s => (varN s >= square (varP s)) /\ (varR s < varP s) /\ Inv s,
         fun _ _ s' => Inv s']).

Definition WPT5b :=
  If (Lt (Var N) (Mult (Var P) (Var P))) WPT5bThen WPT5bElse.

End Definitions.

Module Proof.

Import Definitions.
Import While.CodeGeneration.
Import Bool.

Ltac refine_post pt1 pt2 := apply (Refinement _ _ (fun s (y : pre pt1 s) => y : pre pt2 s)).

Lemma step1 : WSPEC ⊑ WPT1.
  Proof.    
    unfold WSPEC, WPT1, "⊑", semantics. 
    unfold SPEC, PT1, Inv. refine_post SPEC PT1.
    intros X tt s [H1 H2]; simpl in *; rewrite H2; apply H1.    
  Qed.

Lemma step2 : WPT1 ⊑ WPT2.
  Proof.
    unfold WPT1, WPT2, "⊑", semantics. 
    unfold PT1, PT2, Inv, Seq_PT. simpl.
    assert (d : forall s, pre PT1 s -> pre PT2 s).
    intros; exists I; intros; auto.
    apply (Refinement _ _ d).
    simpl; intros s Pre s' [t [H1 [H2 H3]]]; split; auto.
Qed.

Lemma step3 : WPT2 ⊑ WPT3a ; WPT3b.
Proof.
  unfold WPT2,WPT3a,WPT3aa,WPT3ab,WPT3b,"⊑",semantics.
  apply refineSplitPT.
  simpl.
  unfold Assign_PT, K, Inv.
  apply (refineTransPT PT3a).
  (* Part a *)
    unfold K, Inv, PT3a, square; apply refineAssign.
    simpl; intros; split; auto with arith.
  (* refineTrans *)
  unfold PT3a,Assign_PT.
  apply refineSeqAssign.
  intros; destruct s; simpl; reflexivity.
  (* Part b *)
     (* FIXME: use refineWhile? *)
     assert (d: pre ([Inv, fun (s: S) (_: Inv s) (X: S) => Inv X /\ 1 + varR X = varQ X])
                ⊂ pre (semantics WPT3b)).
     unfold WPT3b,subset,pre; simpl; intros; split; try assumption.
     split. 
     split; inversion H0; assumption.
     intros; assumption.
     apply (Refinement _ _ d).
     intros s Pre s' [Post1 Post2]; split; auto.
     case_eq (beq_nat (Datatypes.S (varR s')) (varQ s')).
     intro H; apply (beq_nat_true (Datatypes.S (varR s')) (varQ s') H).
     change (Is_false (negb (beq_nat (Datatypes.S (varR s')) (varQ s')))) in Post2.
     intro F; rewrite F in Post2; contradiction.
Qed.

Axiom lt_n_sq : forall (m n : nat), m < n -> m * m < n * n. 
Axiom lt_sq_n : forall (m n : nat), m * m < n * n -> m < n.

Lemma step4 : WBody ⊑ WPT4.
  unfold WPT3b,WPT4,"⊑",semantics; simpl.

  assert (d: pre (semantics WBody) ⊂ pre (semantics WPT4)).
  unfold subset,pre,semantics,WBody,WPT4.
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


Lemma step5 : WPT4 ⊑ WPT5a ; WPT5b.
  unfold "⊑",semantics. 
  simpl.
  apply refineSplitPT.
  apply refineAssign.
  simpl.
  intros s H.
  split.
  destruct s.
  simpl in *.
  split.
  inversion H as [H1 H2].

 (** even-odd approach **)
  assert (Ha: even varR0 \/ odd varR0).
  apply even_or_odd. destruct Ha as [R0even|R0odd].

  (* varR0 even *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].

  (* varR0 even, varQ0 even *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O.
  rewrite even_plus_div2. rewrite even_plus_div2. apply plus_lt_compat_r.
  apply even_even_lt_div2. split; trivial. apply le_Sn_le in H1. exact H1. trivial. trivial.

  (* varR0 even, varQ0 odd *)
  rewrite plus_comm. rewrite even_plus_div2. rewrite plus_comm. 
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  apply plus_lt_compat_r. apply even_odd_lt_div2. split; trivial. trivial. trivial. trivial.

  (* varR0 odd *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
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
  assert (Ha: even varR0 \/ odd varR0). apply even_or_odd. destruct Ha as [R0even|R0odd].
  (* varR0 even *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
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
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
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

  unfold Inv.
  (* FIXME: use refineIf ? *)
  assert (d: pre ([fun X : S => varR X < varP X < varQ X /\ square (varR X) <= varN X < square (varQ X),
             fun (s : S) (_ : varR s < varP s < varQ s /\ square (varR s) <= varN s < square (varQ s)) 
             (X : S) => square (varR X) <= varN X < square (varQ X)])
             ⊂ pre (semantics WPT5b)).
  unfold pre,semantics,subset,WPT5b; simpl.
  intros s [[H1 H2] [H3 H4]].
  destruct s as [N P Q R]; simpl in *.
  split.
  intros H5; split. 
  unfold Is_true in H5.  
  remember (Compare_dec.leb N (P * P) && negb (beq_nat N (P * P))) as e; destruct e.
  symmetry in Heqe; apply andb_true_iff in Heqe.
  inversion Heqe as [H6 H7].
  apply leb_iff in H6.
  unfold square,"<"; unfold negb in H7.
  remember (beq_nat N (P * P)) as e; destruct e.
  inversion H7.
  symmetry in Heqe0.
  apply beq_nat_false in Heqe0.
  inversion H6.
  contradiction.
  apply le_n_S; assumption.
  exfalso; assumption.
  split; [assumption | unfold Inv; split; assumption].
  intros; split.
  unfold Is_false in H.
  remember (Compare_dec.leb N (P * P) && negb (beq_nat N (P * P))) as e; destruct e.
  exfalso; assumption.
  symmetry in Heqe; apply andb_false_iff in Heqe.
  inversion Heqe as [H5 | H5].
  apply leb_complete_conv in H5.
  unfold square,ge,lt in *; apply le_Sn_le in H5; assumption.
  unfold negb in H5; remember (beq_nat N (P * P)) as e; destruct e.
  symmetry in Heqe0; apply beq_nat_true in Heqe0.
  unfold ge,square in *; symmetry in Heqe0.
  rewrite Heqe0; apply le_n.
  inversion H5.
  split; [assumption | unfold Inv; split; assumption].

  apply (Refinement _ _ d).
  simpl; unfold subset; intros.
  inversion x as [H1 H2].
  unfold Inv in *.
  assert (Ha: forall b, or (Is_true b) (Is_false b)) by 
         (intros; destruct b; simpl in *; auto). 
  destruct s as [N P Q R]; simpl in *.
  inversion H as [H3 H4]. 
  assert (H': or (Is_true (Compare_dec.leb N (P * P) && negb (beq_nat N (P * P))))
                 (Is_false (Compare_dec.leb N (P * P) && negb (beq_nat N (P * P)))))
         by (apply Ha).
  inversion H' as [H5 | H5].
  apply H3 in H5; assumption.
  apply H4 in H5; assumption.
Qed.

Lemma step6Then : WPT5bThen ⊑ Q ::= (Var P).
Proof.
  unfold WPT5bThen,"⊑",semantics.
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

Lemma step6Else : WPT5bElse ⊑ R ::= (Var P).
Proof.
  unfold WPT5bElse,"⊑",semantics.
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 [H2 [H3 H4]]].
  destruct s. unfold Inv in *.
  simpl in *.
  split; auto.
Qed.

Definition prgrm := WPT3a ;
  (While Inv (Not (Eq (Plus (EConst 1) (Var R)) (Var Q)))
         (WPT5a ; (If (Lt (Var N) (Mult (Var P) (Var P))) 
                      (Q ::= (Var P)) 
                      (R ::= (Var P))))).

Theorem result : WSPEC ⊑ prgrm.
Proof.
  apply (refineTrans WPT1); try apply step1.
  apply (refineTrans WPT2); try apply step2.
  apply (refineTrans (WPT3a ; WPT3b)); try apply step3.
  apply refineSplit; try apply refineRefl.
  unfold WPT3b; apply refineBody.
  apply (refineTrans WPT4); try apply step4.
  apply (refineTrans (WPT5a ; WPT5b)); try apply step5.
  apply refineSplit; try apply refineRefl.
  unfold WPT5b; apply refineSplitIf; [apply step6Then | apply step6Else]. 
Qed.

Lemma prgrmProof : isExecutable prgrm.
Proof.  
  unfold prgrm,isExecutable; simpl; auto.
Qed.

Require Import String.
Compute (toCode prgrm prgrmProof 0).

End Proof.

End Example.
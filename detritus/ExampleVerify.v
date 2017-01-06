Require Import Div2.
Require Import Even.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import AuxiliaryProofs.
Require Import Bool.
Require Import While.
Require Import Usability.
Require Import Heap.
Require Import Coq.FSets.FMapFacts.
Import While.Language.
Import While.Semantics.

Module Swap.
Import Bool.

Lemma add_neq_o : forall m x y (e : val),
 ~ M.E.eq x y -> M.find y (M.add x e m) = M.find y m.
Admitted.

Lemma MapsTo_iff : forall m x y (e : Addr.t), M.E.eq x y -> (M.MapsTo x e m <-> M.MapsTo y e m).
Admitted.

Lemma add_neq_mapsto_iff : forall m x y (e e' : Addr.t),
 ~ M.E.eq x y -> (M.MapsTo y e' (M.add x e m) <-> M.MapsTo y e' m).
Admitted.

Lemma find_mapsto_iff : forall m x (e : Addr.t), M.MapsTo x e m <-> M.find x m = Some e.
Admitted.

Lemma mapsto_find : forall m x (e : Addr.t), M.MapsTo x e m -> M.find x m = Some e.
Admitted.

Lemma in_find_iff : forall (m : heap) x, M.In x m <-> M.find x m <> None.
Admitted.

Lemma mem_in_iff : forall (m : heap) (x : Addr.t), M.In x m <-> M.mem x m = true.
Admitted.

Lemma add_eq_b : forall m x y (e : val),
 M.E.eq x y -> M.mem y (M.add x e m) = true.
Admitted.

Lemma add_neq_b : forall m x y (e : val),
 ~M.E.eq x y -> M.mem y (M.add x e m) = M.mem y m.
Admitted.

Lemma add_eq_o : forall m x y (e : val),
 M.E.eq x y -> M.find y (M.add x e m) = Some e.
Admitted.

Lemma add_in_iff : forall m x y (e : val), M.In y (M.add x e m) <-> M.E.eq x y \/ M.In y m.
Admitted.

Definition P : Addr.t := Addr.MkAddr 0.
Definition Q : Addr.t := Addr.MkAddr 1.
Definition N : Addr.t := Addr.MkAddr 2.

Definition SWAP := 
  Spec ([ fun s => M.In P s /\ M.In Q s /\ M.In N s
        , fun s _ s' => find s P = find s' Q
                     /\ find s Q = find s' P
                     /\ M.In P s' 
                     /\ M.In Q s'
                     /\ M.In N s']). 

(*
Definition SWAP := Spec ([fun _ => True, fun s _ s' => varP s = varQ s' /\ varP s' = varQ s]).
*)

Definition swapResult :
  SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N).
Proof.
  apply (refineTrans
          (Spec ([ fun s => M.In P s /\ M.In Q s /\ M.In N s
                 , fun s _ s' => find s Q = find s' N
                              /\ find s P = find s' Q
                              /\ M.In P s' /\ M.In Q s' /\ M.In N s']) ; 
           P ::= Var N)).
  apply refineFollowAssign.

  intros s [PinS [QinS NinS]] s' [eq1 [eq2 [PinS' [QinS' NinS']]]].
  unfold subst; simpl; repeat split.
  unfold setIdent,getIdent,update,find; rewrite add_neq_o; [ assumption | auto].
  unfold setIdent,getIdent,update,find; rewrite add_eq_o; unfold find in eq1.
  rewrite eq1; apply in_find_iff in NinS'.
  destruct (M.find (elt:=val) N s'); [ | contradict NinS']; trivial.
  unfold M.E.eq; trivial.
  
  unfold setIdent,getIdent,update; rewrite mem_in_iff; apply add_eq_b; unfold M.E.eq; trivial.
  unfold setIdent,getIdent,update; rewrite <- eq1; rewrite add_in_iff; right; assumption.
  unfold setIdent,getIdent,update; rewrite add_in_iff; right; assumption.
  assumption.

  apply refineSeqAssocR.
  apply refineSplit; try apply refineRefl.
  apply (refineTrans
          (Spec ([ fun s => M.In P s /\ M.In Q s /\ M.In N s
                 , fun s _ s' => find s P = find s' P 
                              /\ find s Q = find s' N
                              /\ M.In P s' /\ M.In Q s' /\ M.In N s']) ; 
           Q ::= Var P)).
  apply refineFollowAssign.

  intros s [PinS [QinS NinS]] s' [eq1 [eq2 [PinS' [QinS' NinS']]]].
  unfold subst; simpl; repeat split.
  unfold setIdent,getIdent,update,find; rewrite add_neq_o; [ assumption | auto].

  unfold setIdent,getIdent,update,find; rewrite add_eq_o.
  unfold find in eq1; rewrite eq1; apply in_find_iff in PinS'.
  destruct (M.find (elt:=val) P s'); [ | contradict PinS']; trivial.  
  unfold M.E.eq; trivial.

  unfold setIdent,getIdent,update,find; rewrite add_in_iff; right; assumption.
  unfold setIdent,getIdent,update,find; rewrite add_in_iff; left; unfold M.E.eq; trivial.
  unfold setIdent,getIdent,update,find; rewrite add_in_iff; right; assumption.
  assumption.

  apply refineSplit; try apply refineRefl.
  apply refineAssign.
  simpl; intros s [PinS [QinS NinS]]. 

  repeat split. 
  unfold setIdent,getIdent,update,find; rewrite add_neq_o; trivial.
  unfold N, P, M.E.eq; intros contra; inversion contra.

  unfold setIdent,getIdent,update,find; rewrite add_eq_o; rewrite in_find_iff in QinS.
  destruct (M.find (elt:=val) Q s); [ | contradict QinS]; trivial.

  unfold M.E.eq; trivial.
  unfold setIdent,getIdent,update,find; rewrite add_in_iff; right; assumption.
  unfold setIdent,getIdent,update,find; rewrite add_in_iff; right; assumption.
  unfold setIdent,getIdent,update,find; rewrite add_in_iff; right; assumption.

  unfold subset; simpl; intros s [PinS [QinS NinS]]; assumption.
Defined.

End Swap.

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
  inversion H as [H1 H2].
  split.  

  apply plus_lt_compat_r with (p:=R) in H1.
  simpl in H1.
  apply lt_S_div2 in H1.
  replace (R + R) with (2 * R) in H1 by (omega).
  rewrite div2_double in H1.
  assumption.

  apply plus_lt_compat_r with (p:=Q) in H1.
  simpl in H1.
  apply lt_S_div2 in H1.
  replace (Q + Q) with (2 * Q) in H1 by (omega).
  rewrite div2_double in H1.
  rewrite plus_comm in H1.
  assumption.

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

(*
Require Import String.
Compute (whileToCode prgrm prgrmProof).
*)


End Proof.


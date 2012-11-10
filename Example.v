Require Import Div2.
Require Import Even.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import AuxiliaryProofs.
Require Import Bool.
Require Import While.
Require Import Usability.
Require Import ExampleVerify.
Import While.Language.
Import While.Semantics.
Import ExampleVerify.Swap.
Import ExampleVerify.Definitions.
Import ExampleVerify.Proof.

Section StepProofs.

Lemma stepWhileProof :
   forall s : S,
   Is_false (evalBExpr (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) s) ->
   1 + varR s = varQ s.
Proof.
    intros.
    unfold Is_false in H.
    remember (evalBExpr (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) s) as e; destruct e.
    inversion H.
    unfold evalBExpr in Heqe.
    simpl in Heqe.
    destruct s as [N P Q R]; simpl in *.
    unfold negb in Heqe.
    remember (match Q with
              | 0 => false
              | Datatypes.S m1 => beq_nat R m1
              end) as e; destruct e.
    destruct Q as [|Q].
    inversion Heqe0.
    apply beq_nat_eq in Heqe0.
    rewrite Heqe0; reflexivity.
    inversion Heqe.
Qed.

Lemma weakenPreProof :
   (fun s : S =>
    Inv s /\
    Is_true (evalBExpr (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) s))
   ⊂ (fun s : S => 1 + varR s < varQ s /\ Inv s).
Proof.
    unfold subset; intros s [H1 H2].
    split; [ | assumption ].
    case_eq (evalBExpr (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) s).
      unfold Inv in H1; destruct s as [N P Q R]; simpl in *; intros H3; destruct H1 as [H H1].
      apply le_lt_trans with (p := square Q) in H; [ | assumption ].
      apply lt_sq_n in H.
      destruct Q as [|Q]; [ inversion H1 | ].
        case_eq (beq_nat R Q); intros H4.
          rewrite H4 in H3; inversion H3.        
          apply beq_nat_false in H4.
          apply lt_n_S.
          inversion H; [ exfalso; apply H4; assumption | assumption ].
      intros H; rewrite H in H2; inversion H2.
Qed.

Definition Seq1 := Spec
     ([fun s : S => 1 + varR s < varQ s /\ Inv s,
      fun (s : S) (_ : 1 + varR s < varQ s /\ Inv s) (s' : S) => Inv s']).
Definition Seq2 := Spec
       ([fun s : S => 1 + varR s < varQ s /\ Inv s,
        fun (s : S) (_ : 1 + varR s < varQ s /\ Inv s) (s' : S) =>
        varR s' < varP s' < varQ s' /\ Inv s']).
Definition Seq3 := Spec
       ([fun X : S => varR X < varP X < varQ X /\ Inv X,
        fun (s : S) (_ : varR s < varP s < varQ s /\ Inv s) (s' : S) =>
        Inv s']).

Definition seqPTProof :
   Seq1 ⊑ Seq2 ; Seq3.
Proof.
  assert (d: pre (semantics Seq1) ⊂ pre (semantics (Seq2 ; Seq3))).
    unfold subset; simpl; intros.
    exists H; intros; assumption.
  apply (Refinement _ _ d).
  intros s H; unfold subset; simpl; intros s' [s'' [H1 H2]]; assumption.
Qed.

Definition assignProof : forall (N Q R : nat),
  Datatypes.S R < Q /\ square R <= N < square Q ->
  R < div2 (Q + R) < Q /\ square R <= N < square Q.
Proof.
  intros N Q R H; split.
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
  unfold Inv in *; simpl in *.
  split; assumption.  
Qed.

Definition ThenSpec :=
  Spec ([fun s : S => ((varR s < varP s < varQ s /\ Inv s) *
                      Is_true (proj1_sig (nat_lt_ge_bool match s with
                                                         | {| varN := n |} => n
                                                         end
                                                         (match s with
                                                         | {| varP := p |} => p
                                                         end * match s with
                                                               | {| varP := p |} => p
                                                               end))))%type,
         fun (s : S) (_ : (varR s < varP s < varQ s /\ Inv s) *
                          Is_true (proj1_sig
                                  (nat_lt_ge_bool match s with
                                                  | {| varN := n |} => n
                                                  end
                                                  (match s with
                                                  | {| varP := p |} => p
                                                  end * match s with
                                                       | {| varP := p |} => p
                                                       end)))) (s' : S) => Inv s']).

Definition ElseSpec :=
  Spec ([fun s : S => ((varR s < varP s < varQ s /\ Inv s) *
                      Is_false (proj1_sig (nat_lt_ge_bool match s with
                                                          | {| varN := n |} => n
                                                          end
                                                          (match s with
                                                          | {| varP := p |} => p
                                                          end * match s with
                                                                | {| varP := p |} => p
                                                                end))))%type,
         fun (s : S) (_ : (varR s < varP s < varQ s /\ Inv s) *
                          Is_false (proj1_sig (nat_lt_ge_bool match s with
                                                              | {| varN := n |} => n
                                                              end
                                                              (match s with
                                                              | {| varP := p |} => p
                                                              end * match s with
                                                                   | {| varP := p |} => p
                                                                   end)))) (s' : S) => Inv s']).


Lemma w5bThenProof : ThenSpec ⊑ W5bThen.
Proof.
    assert (d: pre (semantics ThenSpec) ⊂ pre (semantics (W5bThen))).
    unfold subset,semantics,Inv; simpl; intros [N P Q R] [[[H1 H2] [H3 H4]] H]; simpl in *.
    unfold Is_true in H; unfold Inv; simpl.
    split.
    remember (proj1_sig (nat_lt_ge_bool N (P * P))) as e; destruct e.
    unfold proj1_sig,nat_lt_ge_bool,Sumbool.bool_of_sumbool,sumbool_rec in *.
    unfold sumbool_rect,Sumbool.sumbool_not in *.
    remember (lt_ge_dec N (P * P)) as e; destruct e.
    assumption.
    inversion Heqe.
    inversion H.
    repeat split; assumption.
    apply (Refinement _ _ d).
    simpl; unfold subset; intros s PreS s' H.
    assumption.
Qed.

Lemma w5bElseProof : ElseSpec ⊑ W5bElse.
Proof.
  assert (d: pre (semantics ElseSpec) ⊂ pre (semantics (W5bElse))).
      unfold subset,semantics,Inv; simpl; intros [N P Q R] [[[H1 H2] [H3 H4]] H]; simpl in *.
      unfold Is_false in H; unfold Inv; simpl in *.
      unfold proj1_sig,nat_lt_ge_bool,Sumbool.bool_of_sumbool,sumbool_rec in *.
      unfold sumbool_rect,Sumbool.sumbool_not in *.
      remember (lt_ge_dec N (P * P)) as e; destruct e.
      inversion H.
      repeat split; assumption.
    apply (Refinement _ _ d).
    unfold subset; simpl; intros; assumption.
Qed.

End StepProofs.

Section Results.

Lemma resultSqrt : 
  { c : WhileL | (WSPEC ⊑ c) /\ isExecutable c }.
Proof.
  apply (step W1).
    apply step1.
  apply stepSeqPT with (Mid := Inv).
    apply step2.
  apply stepFollowAssign with (id := Q) (expr := Plus (EConst 1) (Var N))
          (Q' := fun _ _ s' => (square (varR s') <= varN s' < square (1 + varN s'))).
    intros; destruct s as [N P Q R]; destruct s' as [N' P' Q' R']; simpl in *.
    assumption.
  apply stepAssign with (id := R) (exp := EConst 0).
    unfold square; intros; destruct s as [N P Q R]; simpl in *.
    split; auto with arith.
  apply stepWhile with (cond := (Not (Eq (Plus (EConst 1) (Var R)) (Var Q)))).
    apply stepWhileProof. 
  apply stepWeakenPre with (f := weakenPreProof)
                           (Q := fun (s : S) (_ : 1 + varR s < varQ s /\ Inv s)
                                     (s' : S) => Inv s').
  apply stepSeqPT with (Mid := (fun X => varR X < varP X < varQ X /\ Inv X)).
    apply seqPTProof.
  apply stepAssign with (id := P) (exp := Div2 (Plus (Var Q) (Var R))). 
    unfold subset,Inv; simpl; destruct s as [N P Q R]; simpl in *.
    apply assignProof. 
  apply stepIf with (cond := Lt (Var N) (Mult (Var P) (Var P))).
  apply (step W5bThen); simpl.
    apply w5bThenProof.
  apply stepAssign with (id := Q) (exp := Var P).
    unfold W5bThen,Inv; simpl; intros s [H1 [H2 [H3 H4]]].
    destruct s as [N P Q R]; simpl in *; split; assumption.
  apply (step W5bElse); simpl.
    apply w5bElseProof.
  apply stepAssign with (id := R) (exp := Var P).
    unfold W5bElse,Inv; simpl; intros s [H1 [H2 [H3 H4]]].
    destruct s as [N P Q R]; simpl in *; split; assumption.    
Defined.

Lemma resultSwap : 
  { c : WhileL | ((SWAP ⊑ c) /\ isExecutable c)}.
Proof.
  apply stepFollowAssign with (id := P) (expr := Var N)
                              (Q' := fun s _ s' => varP s = varQ s' /\ varN s' = varQ s).
  destruct s as [N P Q R]; destruct s' as [N' P' Q' R']; simpl; intros; assumption.  
  apply stepFollowAssign with (id := Q) (expr := Var P)
                              (Q' := fun s _ s' => varP s = varP s' /\ varN s' = varQ s).
  destruct s as [N P Q R]; destruct s' as [N' P' Q' R']; simpl; intros; assumption.
  apply stepAssign with (id := N) (exp := Var Q).
  simpl; intros; destruct s as [N P Q R]; simpl; split; reflexivity.
Defined.

Definition sqrtCode : WhileL := proj1_sig resultSqrt.
Definition swapCode : WhileL := proj1_sig resultSwap.

(*
Compute sqrtCode.
Compute swapCode.
*)

(*
Extraction Language Haskell.
Extraction "Program.hs" sqrtprgrm.
*)

End Results.
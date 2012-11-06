Require Import Refinement.
Require Import While.
Require Import Bool.
Import While.Language.
Import While.Semantics.

Lemma stop : forall (w : WhileL),
  isExecutable w ->
  exists (C : WhileL), (w ⊑ C) /\ isExecutable C.
Proof.
  intros w; exists w; split; [apply refineRefl | assumption].
Qed.

Ltac stop :=  
  match goal with  
  | [ |- ex ?C ] => try apply stop; unfold isExecutable; try auto
  end. 

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

Lemma stepSeqPT : forall (Pre Mid Post : Pow S),
  (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ 
    (Spec ([Pre , (fun _ _ s' => Mid s')])) ; (Spec ([Mid , (fun _ _ s' => Post s')]))) ->
  (exists c, (Spec ([Pre , (fun _ _ s' => Mid s')]) ⊑ c) /\ isExecutable c) ->
  (exists c, (Spec ([Mid , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c) ->
  exists c, (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c.
Proof.
  intros Pre Mid Post H1 H2 H3.
  inversion H2 as [c'  [H4 H5]].
  inversion H3 as [c'' [H6 H7]].
  exists (c' ; c'').
  split.
  apply (refineTrans (Spec ([Pre, fun (s : S) (_ : Pre s) (s' : S) => Mid s']);
         Spec ([Mid, fun (s : S) (_ : Mid s) (s' : S) => Post s']))).
  assumption.
  apply refineSplit; assumption.
  simpl; split; assumption.
Qed.

Lemma refineIfPT (P : Pow S) (Q : forall s, P s -> Pow S)
                 (PThen : Pow S) (QThen : forall s, PThen s -> Pow S)
                 (PElse : Pow S) (QElse : forall s, PElse s -> Pow S) 
                 (cond : S -> bool) :
  let pt := ([P,Q]) in
  let Then := ([PThen,QThen]) in
  let Else := ([PElse,QElse]) in
  (forall s, Is_true (cond s) -> pt ⊏ Then) ->
  (forall s, Is_false (cond s) -> pt ⊏ Else) ->
  pt ⊏ If_PT cond Then Else.  
Proof.
  intros pt Then Else H1 H2.
  assert (d : pre pt ⊂ pre (If_PT cond Then Else)).
  unfold pre,semantics,subset; simpl.  
  intros.
  split.
  intros H3.
  apply H1 in H3.
  inversion H3 as [H4 H5]; simpl in H4.
  apply H4 in H; assumption.
  intros H3.
  apply H2 in H3.
  inversion H3 as [H4 H5]; simpl in H4.
  apply H4 in H; assumption.
(*
  unfold subset in d; simpl in d.
  unfold pt,Then in H1. simpl in H1.
*)
  apply (Refinement _ _ d).
  intros.
  unfold subset; intros s' Post.
  simpl.
  simpl in Post.
Admitted.  

Lemma refineIf (P : Pow S) (Q : forall s, P s -> Pow S) (cond : BExpr) (WThen WElse : WhileL) :
  let pt := Spec ([P,Q]) in
  (forall s, Is_true (evalBExpr cond s) -> pt ⊑ WThen) ->
  (forall s, Is_false (evalBExpr cond s) -> pt ⊑ WElse) ->
  pt ⊑ If cond WThen WElse.
Proof.
  intros pt H1 H2.
  apply refineIfPT.
  intros.
  apply H1 in H.
  unfold wrefines,semantics in H.
  simpl in H.
Admitted.

Lemma stepIf (P : Pow S) (Q : forall s, P s -> Pow S) (cond : BExpr) (WThen WElse : WhileL) :
  let pt := Spec ([P,Q]) in
  (forall s, Is_true (evalBExpr cond s) -> pt ⊑ WThen) ->
  (forall s, Is_false (evalBExpr cond s) -> pt ⊑ WElse) ->
  (exists c, (If cond WThen WElse ⊑ c) /\ isExecutable c) ->
  exists c, (pt ⊑ c) /\ isExecutable c.
Proof.
  intros pt H1 H2 [c [H3 H4]].
  exists c.
  split.
  apply (refineTrans (If cond WThen WElse)).
  apply refineIf; unfold pt in *; assumption.
  assumption.
  assumption.
Qed.

Lemma stepWhile (inv : Pow S) (cond : BExpr) (Q : Pow S) : 
  let pt := [inv , fun _ _ s' => inv s' /\ Q s'] in
  let body := [fun s => inv s /\ Is_true (evalBExpr cond s), (fun _ _ s => inv s)] in
  (forall s, Is_false (evalBExpr cond s) -> Q s) ->
  (exists c, (While inv cond (Spec body) ⊑ c) /\ isExecutable c) ->
  exists c, (Spec pt ⊑ c) /\ isExecutable c.
Proof.
  intros pt body H1 [c [H2 H3]].
  exists c.
  split.
  apply (refineTrans (While inv cond (Spec body))).
  unfold wrefines,semantics.
  apply refineWhile.
  apply H1.
  assumption.
  assumption.
Qed.  

Lemma stepBody (inv : Pow S) (cond : BExpr) (bodyL bodyR : WhileL) :
  bodyL ⊑ bodyR ->
  (exists c, (While inv cond bodyR ⊑ c) /\ isExecutable c) ->
  exists c, (While inv cond bodyL ⊑ c) /\ isExecutable c.
Proof.
  intros H1 [c [H2 H3]].
  exists c.
  split.
  apply (refineTrans (While inv cond bodyR)).
  apply refineBody; assumption.
  assumption.
  assumption.
Qed.
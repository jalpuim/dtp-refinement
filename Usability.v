Require Import Refinement.
Require Import While.
Require Import Bool.
Require Import Heap.
Import While.Language.
Import While.Semantics.

(* refineRefl equiv *)
Lemma stop {w} :
  isExecutable w ->
  { c : WhileL | (w ⊑ c) /\ isExecutable c }.
Proof.
  exists w; split; [apply refineRefl | assumption].
Defined.

Ltac stop := try apply stop; unfold isExecutable; try auto.

(* refineTrans equiv *)
Lemma step {SPEC} (R : WhileL) :
  SPEC ⊑ R ->
  {C : WhileL | ((R ⊑ C) /\ isExecutable C)} -> 
  {C : WhileL | ((SPEC ⊑ C) /\ isExecutable C)}.
Proof.
  intros H1 H2.
  inversion H2 as [w [H3 H4]].
  exists w.
  split; try apply (refineTrans R); assumption.
Defined.

Lemma stepSplit {w1 w2} :
  {c : WhileL | (w1 ⊑ c) /\ isExecutable c} ->
  {c : WhileL | (w2 ⊑ c) /\ isExecutable c} ->
  {c : WhileL | ((w1 ; w2) ⊑ c) /\ isExecutable c}.
Proof.
  intros [c1 [H1 H2]] [c2 [H3 H4]].
  exists (c1 ; c2).
  split.
  apply refineSplit; assumption.
  simpl; split; assumption.
Defined.

Lemma stepSplitIf {w1 w2 cond} :
  {c : WhileL | (w1 ⊑ c) /\ isExecutable c} -> 
  {c : WhileL | (w2 ⊑ c) /\ isExecutable c} ->
  {c : WhileL | (If cond w1 w2 ⊑ c) /\ isExecutable c}.
Proof.
  intros [c1 [H1 H2]] [c2 [H3 H4]].
  exists (If cond c1 c2).
  split.
  apply refineSplitIf; assumption.
  simpl; split; assumption.
Defined.

Lemma stepAssign {w} (id : Identifier) (exp : Expr) 
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre ((setIdent id (evalExpr exp s)) s)) (h' : pre (semantics w) ⊂ (fun h => M.In id h)) :
  { c : WhileL | (w ⊑ c) /\ isExecutable c}.
Proof.
  exists (Assign id exp).
  split.
  apply refineAssign; assumption.
  simpl; trivial.
Defined.

Lemma stepFollowAssign {P : Pow S} {Q} (id : Identifier) (expr : Expr)
(Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec ([P,Q]) in
  let w' := Spec ([P,Q']) in
  (forall s pres s', Q' s pres s' -> prod (Q s pres (subst id expr s')) (M.In id s')) ->
  {c : WhileL | (w' ⊑ c) /\ isExecutable c } -> 
  {c : WhileL | (w ⊑ c) /\ isExecutable c }.
Proof.
  intros w w' HQ [c [H2 H3]].
  apply refineFollowAssign in HQ.
  apply (step (w' ; id ::= expr)).
  assumption.
  apply stepSplit.
  exists c.
  simpl; split; [assumption | trivial].
  exists (id ::= expr).
  split.
  apply refineRefl.
  simpl.
  trivial.
Defined.

Lemma stepSeqPT {Pre Post} (Mid : Pow S) :
  (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ 
    (Spec ([Pre , (fun _ _ s' => Mid s')])) ; (Spec ([Mid , (fun _ _ s' => Post s')]))) ->
  { c : WhileL | (Spec ([Pre , (fun _ _ s' => Mid s')]) ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec ([Mid , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c }.
Proof.
  intros H1 [c1 [H2 H3]] [c2 [H4 H5]].
  apply (step (Spec ([Pre, fun (s : S) (_ : Pre s) (s' : S) => Mid s']);
               Spec ([Mid, fun (s : S) (_ : Mid s) (s' : S) => Post s']))).
  assumption.
  exists (c1 ; c2).
  split.
  apply refineSplit; assumption.
  simpl; split; assumption.
Defined.

Lemma stepIf (cond : BExpr) (pt : PT) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := Spec ([branchPre (fun s => Is_true (evalBExpr cond s)),
                           fun s pre s' => post pt s (fst pre) s' ]) in
  let elseBranch := Spec ([branchPre (fun s => Is_false (evalBExpr cond s)),
                           fun s pre s' => post pt s (fst pre) s' ]) in
  { c : WhileL | (thenBranch ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (elseBranch ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec pt ⊑ c) /\ isExecutable c }.
Proof.
  intros branchPre thenBranch elseBranch [cThen [H1 H2]] [cElse [H3 H4]].
  exists (If cond cThen cElse).
  split.
  apply (refineTrans (If cond thenBranch elseBranch)).
  apply refineIf.
  apply refineSplitIf; assumption.
  simpl; split; assumption.
Defined.

Lemma stepBody {inv cond bodyL} :
  { c : WhileL | (bodyL ⊑ c) /\ isExecutable c } -> 
  { c : WhileL | (While inv cond bodyL ⊑ c) /\ isExecutable c }.  
Proof.
  intros [c [H2 H3]].
  exists (While inv cond c).
  split.  
  apply refineBody with (inv := inv) (cond := cond) in H2; assumption.
  simpl; assumption.
Defined.

Lemma stepWhile {inv Q} (cond : BExpr) :
  let pt := [inv , fun _ _ s' => inv s' /\ Q s'] in
  let body := [fun s => inv s /\ Is_true (evalBExpr cond s), (fun _ _ s => inv s)] in
  (forall s, Is_false (evalBExpr cond s) -> Q s) ->
  { c : WhileL | (Spec body ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec pt ⊑ c) /\ isExecutable c }.
Proof.
  intros pt body H1 [c [H2 H3]].
  apply (step (While inv cond (Spec body))).
  apply refineWhile; assumption.
  apply stepBody.
  exists c; split; assumption.
Defined.

Lemma stepStrengthenPost {P : Pow S} {Q2} (Q1 : forall s, P s -> Pow S) :
  (forall (s : S) (p : P s), Q1 s p ⊂ Q2 s p) -> 
  { c : WhileL | (Spec ([P , Q1]) ⊑ c) /\ isExecutable c } -> 
  { c : WhileL | (Spec ([P , Q2]) ⊑ c) /\ isExecutable c }.
Proof.
  intros H1 [c [H2 H3]].
  exists c.
  split; [ | assumption].
  apply (refineTrans (Spec ([P , Q1]))); [ | assumption].
  apply strengthenPost; assumption.
Defined.

Lemma stepWeakenPre {P1} {Q} (P2 : Pow S) (f : P1 ⊂ P2) :
  let Q'  := (fun s _ => Q s) in
  let Q'' := (fun s _ => Q s) in
  { c : WhileL | (Spec ([ P2 , Q'' ]) ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec ([ P1 , Q' ]) ⊑ c) /\ 
                 isExecutable c }.
Proof.
  intros Q' Q'' [c [H1 H2]].
  exists c.
  split; [ | assumption ].
  apply (refineTrans (Spec ([ P2 , Q'' ]))); [ | assumption ].
  unfold Q',Q''; apply weakenPre; exact f.
Defined.

Lemma stepSeqAssocL : forall (w1 w2 w3 : WhileL),
  { c : WhileL | ((w1 ; w2) ; w3 ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (w1 ; w2 ; w3 ⊑ c) /\ isExecutable c }.
Proof.
  intros w1 w2 w3 [c [H1 H2]].
  exists c.
  split; [ | assumption].
  apply (refineTrans ((w1; w2); w3)); [ | assumption ].
  apply refineSeqAssocL; apply refineRefl.
Defined.  

Lemma stepSeqAssocR : forall (w1 w2 w3 : WhileL),
  { c : WhileL | (w1 ; w2 ; w3 ⊑ c) /\ isExecutable c } ->
  { c : WhileL | ((w1 ; w2) ; w3 ⊑ c) /\ isExecutable c }.
Proof.
  intros w1 w2 w3 [c [H1 H2]].
  exists c.
  split; [ | assumption].
  apply (refineTrans (w1; w2; w3)); [ | assumption ].
  apply refineSeqAssocR; apply refineRefl.
Defined.
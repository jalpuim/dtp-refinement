Require Import Refinement.
Require Import While.
Require Import Bool.
Import While.Language.
Import While.Semantics.

(* refineRefl equiv *)
Lemma stop : forall (w : WhileL),
  isExecutable w ->
  { c : WhileL | (w ⊑ c) /\ isExecutable c }.
Proof.
  intros w; exists w; split; [apply refineRefl | assumption].
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

Lemma stepSplit (w1 w2 : WhileL) :
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

Lemma stepSplitIf (w1 w2 : WhileL) (cond : BExpr) :
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

Lemma stepAssign (w : WhileL) (id : Identifier) (exp : Expr) 
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre ((setIdent id (evalExpr exp s)) s)) :
  { c : WhileL | (w ⊑ c) /\ isExecutable c}.
Proof.
  exists (Assign id exp).
  split.
  apply refineAssign; assumption.
  simpl; trivial.
Defined.

Lemma stepFollowAssign (id : Identifier) (expr : Expr) (P : Pow S)
(Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec ([P,Q]) in
  let w' := Spec ([P,Q']) in
  (forall s pres s', Q' s pres s' -> Q s pres (subst id expr s')) ->
  {c : WhileL | (w' ⊑ c) /\ isExecutable c } -> 
  {c : WhileL | (w ⊑ c) /\ isExecutable c}.
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

Lemma stepSeqPT : forall (Pre Mid Post : Pow S),
  (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ 
    (Spec ([Pre , (fun _ _ s' => Mid s')])) ; (Spec ([Mid , (fun _ _ s' => Post s')]))) ->
  { c : WhileL | (Spec ([Pre , (fun _ _ s' => Mid s')]) ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec ([Mid , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (Spec ([Pre , (fun _ _ s' => Post s')]) ⊑ c) /\ isExecutable c }.
Proof.
  intros Pre Mid Post H1 [c1 [H2 H3]] [c2 [H4 H5]].
  apply (step (Spec ([Pre, fun (s : S) (_ : Pre s) (s' : S) => Mid s']);
               Spec ([Mid, fun (s : S) (_ : Mid s) (s' : S) => Post s']))).
  assumption.
  exists (c1 ; c2).
  split.
  apply refineSplit; assumption.
  simpl; split; assumption.
Defined.

Lemma stepIf (P : Pow S) (Q : forall s, P s -> Pow S) (cond : BExpr) (WThen WElse : WhileL) :
  let pt := Spec ([P,Q]) in
  (forall s, Is_true (evalBExpr cond s) -> pt ⊑ WThen) ->
  (forall s, Is_false (evalBExpr cond s) -> pt ⊑ WElse) ->
  { c : WhileL | (If cond WThen WElse ⊑ c) /\ isExecutable c } ->
  { c : WhileL | (pt ⊑ c) /\ isExecutable c }.
Proof.
  intros pt H1 H2 [c [H3 H4]].
  apply (step (If cond WThen WElse)).
  apply refineIf; unfold pt in *; assumption.
  exists c; split; assumption.
Defined.

Lemma stepBody (inv : Pow S) (cond : BExpr) (bodyL : WhileL) :
  { c : WhileL | (bodyL ⊑ c) /\ isExecutable c } -> 
  { c : WhileL | (While inv cond bodyL ⊑ c) /\ isExecutable c }.  
Proof.
  intros [c [H2 H3]].
  exists (While inv cond c).
  split.  
  apply refineBody with (inv := inv) (cond := cond) in H2; assumption.
  simpl; assumption.
Defined.

Lemma stepWhile (inv : Pow S) (cond : BExpr) (Q : Pow S) :
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

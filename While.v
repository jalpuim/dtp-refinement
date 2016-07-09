Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Heap.
Require Import Refinement.
Require Import Program.Tactics.
Require Import Program.Equality.

(*******************************************************************************
                    ****   The While language ****
*******************************************************************************)

Definition Ptr := Addr.t.

Inductive WhileL (a : Type) : Type :=
  | New    : forall v, v -> (Ptr -> WhileL a) -> WhileL a
  | Read   : forall v, Ptr -> (v -> WhileL a) -> WhileL a
  | Write  : forall v, Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S -> Prop) -> (S -> bool) -> WhileL unit -> WhileL a -> WhileL a
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "addr ≔ exp" := (Write id addr) (at level 52).

Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
    | New _ _ v k =>
      let pre := fun s => 
                  { ptr : Ptr & prod (find s ptr = None)
                              (pre (semantics (k ptr)) (update s ptr (dyn _ v))) } in 
      let post := fun s pres v' s' => 
                    post (semantics (k (projT1 pres))) (update s (projT1 pres) (dyn _ v)) (snd (projT2 pres)) v' s' in
      
      [pre , post]                                                    
    | Read _ b ptr k =>
      let readPre := fun h => { v : b & find h ptr = Some (dyn b v)} in
      let pre := fun s => {p : readPre s & pre (semantics (k (projT1 p))) s} in
      let post := fun s pres x s' => 
                    post (semantics (k (projT1 (projT1 pres)))) s (projT2 pres) x s' in
      [pre , post]
    | Write _ b ptr v k => 
      let pre := fun s => 
                   prod ({v : b & find s ptr = Some (dyn b v)})
                        (pre (semantics k) (update s ptr (dyn _ v))) in
      let post := fun s pres x s' =>
                    post (semantics k) (update s ptr (dyn _ v)) (snd pres) x s' in
      [pre , post]
    | While _ inv c body k => SeqPT (WhilePT inv c (semantics body)) (@semantics a k)
    | Spec _ s => s
    | Return _ x => Predicate _ (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition preConditionOf {a : Type} (w : WhileL a) : Pow S :=
  match semantics w with
    | Predicate _ p _ => p
  end.

Definition postConditionOf {a : Type} (w : WhileL a)
  : (forall s : S, preConditionOf w s -> a -> Pow S) :=
  match semantics w as x return (forall s : S, match x with | [p, _] => p end s -> a -> Pow S) with
    | [pre, post] => post
  end.

Fixpoint bind {a b : Type} (w : WhileL a) (k : a -> WhileL b) {struct w} : WhileL b :=
  match w with
  | New _ _ v c  => New _ _ v (fun p => bind (c p) k)
  | Read _ _ p c => Read _ _ p (fun v => bind (c v) k)
  | Write _ _ p v c => Write _ _ p v (bind c k)
  | While _ Inv cond body c => While _ Inv cond body (bind c k)
  | Spec _ pt => Spec _ (BindPT pt (fun x => semantics (k x)))
  | Return _ x => k x
  end.

Notation "a ; b" := (bind a (fun _ => b)) (at level 60).

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ _ _ k     => forall ptr, isExecutable (k ptr)
    | Read _ _ _ k    => forall v, isExecutable (k v)
    | Write _ _ _ _ w   => isExecutable w
    | While _ inv c b k => isExecutable b /\ isExecutable k
    | Spec _ pt       => False
    | Return _ a      => True
  end.

Definition wrefines {a : Type} (w1 w2 : WhileL a) := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.


(*******************************************************************************
                   ****   Basic automation ****
*******************************************************************************)


Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.
Ltac refine_unfold := unfold pre, post, subset, bind, "⟫="   in *.
Ltac destruct_refines :=
  match goal with
    | p : ?Refinement _ |- _ => destruct p
  end.
Ltac destruct_pts :=
  match goal with
    | pt : ?PT _ |- _ => destruct pt
  end.
Ltac refine_simpl := 
  refine_unfold; intros; simpl in *; destruct_conjs; 
  repeat split; repeat subst; simpl in *.
Ltac semantic_trivial := 
  unfold semantics, pre, post; simpl; destruct_conjs; repeat split; now intuition.
Ltac exists_now :=
   match goal with
    | x : ?t |- { y : ?t & _} => exists x
    | x : ?t |- { y : ?t | _} => exists x
    | _ => idtac
   end.
Ltac refine_trivial := unfold_refinements; refine_unfold; simpl in *; now intuition.


(*******************************************************************************
                   ****   Refinement properties ****
*******************************************************************************)

Definition refineTrans {a} (w2 w1 w3 : WhileL a) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold_refinements; now apply refineTransPT.
  Defined.

Definition refineRefl {a} (w : WhileL a) :
  w ⊑ w.
    unfold_refinements; apply refineReflPT.
  Defined.

(*******************************************************************************
                   ****   Refinement properties ****
*******************************************************************************)

Lemma newStep {a b : Type} (w : WhileL a) (w' : Ptr -> WhileL a)
  (v : b)
  (H : pre (semantics w) ⊂ pre (semantics (New _ _ v w')))
  (Q : forall (s : S) (x : pre (semantics w) s) (v' : a),
   post (semantics (New _ _ v w')) s (H s x) v' ⊂ post (semantics w) s x v')
  : w ⊑ New _ _ v w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma readStep {a b : Type} (w : WhileL a) (w' : b -> WhileL a)
  (ptr : Ptr)
  (H : pre (semantics w) ⊂ pre (semantics (Read a b ptr w')))
  (Q : forall s p x s', 
         post (semantics (w' (projT1 (projT1 (H s p))))) s (projT2 (H s p)) x s' 
         -> post (semantics w) s p x s')
  : w ⊑ Read _ b ptr w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma readSpec {a b : Type} (ptr : Ptr)  (spec : PT a) (w' : b -> WhileL a)
  (H : forall s, pre (spec) s -> {v : b & find s ptr = Some (dyn b v)})
  (Step : forall v, Spec _ ([ fun s => prod (pre spec s)
                                 (find s ptr = Some (dyn b v))
                       , fun s pres x s' => post spec s (fst pres) x s' ]) ⊑ w' v) :
  Spec _ spec ⊑ Read _ b ptr w'.
Proof.
  eapply readStep. Unshelve. Focus 2.
  * refine_simpl.
    assert (valid : {v : b & find s ptr = Some (dyn b v)}) by now apply H.
    exists valid.
    destruct valid as [v P]; destruct (Step v) as [d h].
    refine_simpl.
    destruct (semantics (w' v)).
    destruct spec.
    apply d; split; auto.
  * intros s p x s' X; destruct spec; refine_simpl.
    generalize X; generalize (H s p).
    intros A.
    intros B.
    destruct A as [A1 A2].
    simpl in *.
    refine_simpl.
    destruct (Step A1) as [d h].
    refine_simpl.
    destruct (semantics (w' A1)).
    set (Ha := pair p A2 : (pre s * (find s ptr = Some (dyn b A1)))).
    pose (h s Ha x s').
    simpl in p2.
    apply p2.
    apply B.
Qed.


Lemma newSpec {a b : Type} (v : b) (spec : PT a) (w : Ptr -> WhileL a)
      (H : forall s, pre spec s -> pre spec (update s (alloc s) (dyn b v)))
      (Step : forall p,
                Spec _ ([ fun s => { t : S & prod (pre spec t)
                                            (prod (forall p', M.In p' t -> p' <> p)
                                                  (s = (update t p (dyn b v)))) }
                        , fun s pres v s' => post spec (projT1 pres) (fst (projT2 pres)) v s' ]) ⊑ w p) :
  Spec _ spec ⊑ New _ b v w.
Proof.
  eapply newStep. Unshelve. Focus 2.
  * refine_simpl;
    exists (alloc s); split;
    destruct (Step (alloc s)) as [d h];
    [ apply allocFresh |
      apply d; destruct spec; simpl in * ].
    exists s.
    repeat split; auto.
    unfold not; intros p' HIn HEq; subst. apply (allocNotIn _ HIn).
  * refine_simpl.
    destruct spec.
    destruct (Step (alloc s)).
    destruct (semantics (w (alloc s))).
    simpl in *.
    apply s1 in X.
    now simpl in X.
Qed.

Lemma writeStep {a b : Type} (w w' : WhileL a) (ptr : Ptr) (v : b)
  (d : pre (semantics w) ⊂ pre (semantics (Write _ _ ptr v w'))) 
  (h : forall (s : S)(p : pre (semantics w) s)  (x : a) (s' : S), 
    post (semantics w') (update s ptr (dyn b v)) (snd (d s p)) x s' -> post (semantics w) s p x s')
  : w ⊑ Write _ _ ptr v w'.
  Proof.
    exact (Refinement _ _ d h).
  Qed.

Lemma writeSpec {a b : Type} (ptr : Ptr) (v : b) (spec : PT a) (w : WhileL a)
  (H : forall s, pre spec s -> {v : b & find s ptr = Some (dyn b v)})
  (Step :  Spec _
    ([ fun s => {t : S & prod (pre spec t) (s = (update t ptr (dyn b v)))},
       fun s pres x s' => 
              (post spec (projT1 pres) (fst (projT2 pres)) x s') ]) ⊑ w) :
  Spec _ spec ⊑ Write _ b ptr v w.
Proof.
  destruct Step as [d h]; eapply writeStep. Unshelve. Focus 2.
  * refine_simpl; destruct spec; [ now apply H | apply d; now exists s].
  * refine_simpl.
    destruct spec.
    destruct (semantics w).
    pose (h _ _ _ _ X).
    now simpl in p2.
Qed.

Lemma returnStep {a : Type} (w : WhileL a) (v : a)
  (H : forall (s : S) (pre : preConditionOf w s), postConditionOf w s pre v s) : 
  w ⊑ Return a v.
Proof.
  eapply Refinement. refine_simpl; apply H.
  Unshelve. refine_simpl.
Qed.

Lemma changeSpec {a : Type} (pt2 pt1 : PT a) (w : WhileL a)
  (d : pre pt1 ⊂ pre pt2)
  (h : forall (s : S) (x : pre pt1 s) v, post pt2 s (d s x) v ⊂ post pt1 s x v)
  (H : Spec _ pt2 ⊑ w) :
  Spec _ pt1 ⊑ w.
  Proof.
    eapply refineTrans; [ | apply H].
    exact (Refinement _ _ d h).
  Qed.

(** Just a brief example showing how the language currently looks like 
    Contains some testing definitions to be moved elsewhere once proven.
**)
Definition SWAP {a : Type} (p q : Ptr): WhileL unit.
  refine (Spec _ _).
  refine (Predicate _ (fun s => prod {x : a | find s p = Some (dyn a x)} {y : a | find s q = Some (dyn a y)}) _).
  intros s H t s'.
  refine (find s p = find s' q /\ find s q = find s' p).
Defined.


  
(************************************************************

                             SWAP EXAMPLE

*************************************************************)

  

Definition refineIf {a} (cond : bool) (pt : PT a) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  (Spec a pt) ⊑ if cond then (Spec a thenBranch) else (Spec a elseBranch).
Proof.
  unfold_refinements; destruct cond; simpl;
  set (d := (fun s pres => pair pres I) : pre pt ⊂ pre ([fun s : S => (pre pt s * True)%type,
                                        fun (s : S) (pre : pre pt s * True) (s' : a) => post pt s (fst pre) s']));
  apply (Refinement _ _ d); intros; destruct_pt a; auto.
Defined.

Lemma refineWhilePT {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) : 
  let pt := [inv , fun _ _ _ s' => inv s' /\ Q s'] in
  let body : PT a := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  (forall s, Is_false (cond s) /\ inv s -> Q s) ->
  pt ⊏ WhilePT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (WhilePT inv cond body)) by
      (refine_simpl; repeat split; destruct_conjs; auto).
    apply (Refinement _ _ d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.

Ltac heap_simpl := try (rewrite findAlloc1, findAlloc2 in * || rewrite findUpdate in * || rewrite findNUpdate1 in * || rewrite findNUpdate2 in *).
Ltac goal_simpl :=  refine_simpl; heap_simpl; eauto.
Ltac READ ptr v := eapply (readSpec ptr); [ | intros v]; goal_simpl.
Ltac NEW v ptr := eapply (newSpec v); [ | intros ptr]; goal_simpl.
Ltac WRITE ptr v := eapply (writeSpec ptr v); goal_simpl.
Ltac ASSERT P := unshelve eapply (changeSpec P).
Ltac RETURN := eapply returnStep; unfold_refinements; goal_simpl.

(* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
Definition swapResult (P : Ptr) (Q : Ptr) (D : P <> Q) (a : Type) :
  let SetQinN (s : Ptr -> WhileL unit) :=
      (Read _ a Q) (fun v => New _ _ v s) in
  let SetPinQ (s : WhileL unit) :=
      (Read _ a P) (fun v => Write _ _ Q v s) in
  let SetNinP (N : Ptr) (s : WhileL unit) :=
      (Read _ a N) (fun v => Write _ _ P v s) in
  @SWAP a P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))).
Proof.
  READ Q x.
  NEW x T.
  READ P y.
  WRITE Q y.
  READ T z.
  WRITE P z.
  RETURN.
  eapply findNUpdate2; [ eauto | ].
  rewrite findUpdate.
  rewrite <- e2.
  apply findNUpdate1.
  eauto.
  reflexivity.
  rewrite <- e0.
  eapply findNUpdate2; [ eauto | ].
  now rewrite findUpdate.
Qed.

Definition swapResult' (P : Ptr) (Q : Ptr) (D : P <> Q) (a : Type) :
  let SetQinN (s : Ptr -> WhileL unit) :=
      (Read _ a Q) (fun v => New _ _ v s) in
  let SetPinQ (s : WhileL unit) :=
      (Read _ a P) (fun v => Write _ _ Q v s) in
  let SetNinP (N : Ptr) (s : WhileL unit) :=
      (Read _ a N) (fun v => Write _ _ P v s) in
  @SWAP a P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))).
Proof.
  READ Q x.
  NEW x T.
  READ P y.
  WRITE Q y.
  ASSERT ([fun s => {v : a & prod (find s T = Some (dyn a v)) 
                                       ({v' : a | find s P = Some (dyn a v')})}
                     , fun s pres (v : unit) s' => find s' P = find s T /\ find s Q = find s' Q ]); [ refine_simpl; exists x; split; eauto | | ].
  { 
    refine_simpl.
    rewrite <- H0; rewrite findUpdate; rewrite <- e0.
    now apply findNUpdate2; eauto.
    rewrite H.
    apply findNUpdate2; eauto.
    now rewrite findUpdate.
  }
  READ T z.
  WRITE P z.
  RETURN.
Qed.

Definition simplSwapDumb (P : Ptr) (Q : Ptr) (D : P <> Q) (a : Type) :
  let CODE :=
      (Read _ a Q) (fun q => 
       Read _ a P (fun p =>
       Write _ _ Q p (
       Write _ _ P q (Return _ tt))))
  in @SWAP a P Q ⊑ CODE.
  intros CODE; unfold CODE.
  unfold wrefines.
  refine_simpl.
  unshelve eapply Refinement.
  refine_simpl.
  now exists s1.
  refine (existT _ (existT _ s0 _) _).
  split.
  now exists_now.
  split.
  exists s0.
  eapply findNUpdate1.
  eauto.
  trivial.
  trivial.
  refine_simpl.
  apply findNUpdate2; eauto.
  now rewrite findUpdate.
  now rewrite findUpdate.
  Unshelve.
  trivial.
  Qed.

Definition simplSwap (P : Ptr) (Q : Ptr) (D : P <> Q) (a : Type) :
  let CODE :=
      (Read _ a Q) (fun q => 
       Read _ a P (fun p =>
       Write _ _ Q p (
       Write _ _ P q (Return _ tt))))
  in @SWAP a P Q ⊑ CODE.
  intros CODE; unfold CODE.
  READ Q q.
  READ P p.
  WRITE Q p.
  WRITE P q.
  RETURN.
  apply findNUpdate2; [eauto | ].
  now rewrite findUpdate.
  Qed.
(** End of example **)

(*******************************************************************************
                ****  Union-Find refinement example ****
*******************************************************************************)

(* Attempt following "A Persistent Union-Find Data Structure" *)

Set Implicit Arguments.
Require Export Wf_nat.

Inductive data : Type :=
  | Arr : (nat -> nat) -> data
  | Diff : nat -> nat -> Ptr -> data.

(* Updates an array at index i with v. I don't know why they used integers 
instead of naturals (maybe to avoid clashes?) *)
Definition upd (f : nat -> nat) (i : nat) (v : nat) := 
  fun j => if beq_nat j i then v else f j.

(* 
   pa_valid states that, given a pointer "p", we either have: 
   1. p points to the original array "Arr"
   2. p points to different "Diff", which is a change of another valid array,
      in one position only.
*)
Inductive pa_valid (s : heap) : Ptr -> Type :=
  | array_pa_valid : forall l p, find s p = Some (dyn data (Arr l)) -> pa_valid s p
  | diff_pa_valid : forall p i v p', find s p = Some (dyn data (Diff i v p')) ->
                                pa_valid s p' ->
                                pa_valid s p.

(* 
   pa_model states that, given a pointer "p", we either have: 
   1. p points to the original array "Arr", with elements given by (Z -> Z)
   2. p points to different "Diff", which is a change of another valid array,
      in one position only, updating the other array in that position (using upd)
*)
Inductive pa_model (s : heap) : Ptr -> (nat -> nat) -> Type :=
  | pa_model_array :
     forall p f, find s p = Some (dyn data (Arr f)) -> pa_model s p f
  | pa_model_diff :
     forall p i v p', find s p = Some (dyn data (Diff i v p')) ->
                   forall f, pa_model s p' f ->
                        pa_model s p (upd f i v).

Lemma pa_model_pa_valid :
  forall m p f, pa_model m p f -> pa_valid m p.
Proof.
  induction 1.
  eapply array_pa_valid; eauto.
  apply diff_pa_valid with (i:=i) (v:=v) (p':=p'); auto.
Qed.

(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
*)

Definition get'' (ptr : Ptr) (i : nat) : WhileL nat.
refine (
  Read _ data ptr (fun vInPtr =>
  New _ data vInPtr (fun t =>
  New _ (option nat) None (fun done =>
      While _ (fun s => True)
              (fun s => _ ) (* find s done Nat.eqb (dyn _ None) *)
              (Read _ data t (fun vInT => _ ))
              (Read _ (option nat) done
                    (fun vInDone => match vInDone with
                                     | None => Return _ 0 (* absurd *)
                                     | Some a => Return _ a
                                   end)))))).
admit. (* TODO how do to defined boolean equality on dynamic *)
destruct vInT as [ f | j v t' ].
refine (Write _ _ done (Some (f i)) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write _ _ done (Some v) (Return _ tt)).
refine (Read _ data t' (fun vInT' => Write _ (option data) done (Some vInT')
                                          (Return _ tt))).
Admitted.

Definition newRef {a} (v : a) : WhileL Ptr :=
  New _ _ v (fun ptr => Return _ ptr).

(* The original set implementation (i.e. no path compression), 
presented in Page 3 *)
Definition set (t : Ptr) (i : nat) (v : nat) : WhileL Ptr :=
  Read _ data t (fun vInT =>
  match vInT with
  | Arr f => New _ _ (Arr (upd f i v))
                (fun res => Write _ data t (Diff i (f i) res) (Return _ res))
  | Diff _ _ _ => newRef (Diff i v t)
  end).

Definition getSpec : Ptr -> nat -> WhileL nat.
  intros ptr i.
  refine (Spec _ _).
  refine (Predicate _ (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] v.
  refine (fun s' => prod (s = s') (v = f i)).
Defined.

Definition setSpec (ptr : Ptr) (i : nat) (v : nat) : WhileL Ptr.
  refine (Spec _ _).
  refine (Predicate _ (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] newPtr s'.
  apply (prod (pa_model s' newPtr (upd f i v))
              (pa_model s' ptr f)).
Defined.

Lemma pa_model_diff_2 :
  forall p : Ptr, forall i v p', forall f f' s,
  find s p = Some (dyn data (Diff i v p')) -> 
  pa_model s p' f' ->
  f = upd f' i v ->
  pa_model s p f. 
Proof.
Admitted.

Axiom upd_ext : forall f g: nat -> nat, (forall i, f i = g i) -> f=g.

Lemma upd_eq : forall f i j v, i=j -> upd f i v j = v.
Proof.
Admitted.
  
Lemma setRefinement : forall ptr i v, setSpec ptr i v ⊑ set ptr i v.
Proof.
  intros; unfold set, setSpec.
  READ ptr vInPtr.
  inversion X0; eauto.
  destruct vInPtr as [ f | j vInJ t' ].
  - NEW (Arr (upd f i v)) res.
    inversion X; subst.
    assert (s0 = f) by admit. (* provable *)
    subst; clear e.
    exists f.
    apply pa_model_array.
    rewrite findAlloc1; auto.
    now apply someIn in H.
    admit. (* contradiction in e and H *)

    (* WRITE ptr (Diff i (f i) ptr). *)
    eapply writeSpec.
    refine_simpl; heap_simpl.
    inversion X0; subst.
    assert (s0 = f) by admit. (* provable *)
    subst; clear e0.
    exists (Arr f).
    rewrite findNUpdate1 with (x := Some (dyn data (Arr f))); auto.
    apply n.
    now apply someIn in H.
    admit. (* contradiction in e and H *) 
    
    RETURN.
    inversion X; subst.
    assert (s1 = f) by admit. (* provable *)
    subst; clear e1.
    apply pa_model_array.
    erewrite findNUpdate1 with (x := Some (dyn data (Arr (upd f i v)))); auto.
    admit. (* provable *)
    admit. (* contradiction in e1 and H *)
    inversion X; subst.
    assert (s1 = f) by admit. (* provable *)
    subst; clear e1.
    apply pa_model_diff_2 with (i := i) (v := f i) (p := ptr) (p' := res)
                                       (f' := upd f i v); auto.
    apply pa_model_array; eauto.
    admit. (* provable *)
    admit. (* contradiction in e1 and H *)
  - unfold newRef.

    NEW (Diff i v ptr) res.
    inversion X; subst.
    admit. (* contradiction in e and H *)
    assert (Ha : (Diff i0 v0 p') = (Diff j vInJ t')).
    admit. (* provable *)
    inversion Ha; subst; clear Ha e.
    exists (upd f j vInJ). Print pa_model_diff.
    apply pa_model_diff with (p := ptr) (p' := t').
    rewrite findAlloc1; auto.
    now apply someIn in H.
    admit. (* looks provable through X0 *)

    RETURN.
Admitted.

(* STOP HERE *)

    
Fixpoint get' (n : nat) (ptr : Ptr) (i : nat) : WhileL nat := 
  Read _ data ptr
       (fun ptrVal => match n, ptrVal with
                       | 0, Arr => Return _ (parray i)
                       | Coq.Init.Datatypes.S n', Diff j v ptr' =>
                         if beq_nat i j
                         then Return _ v
                         else get' n' ptr' i
                       | _,_ => Return _ (parray i) (* absurd *)
                     end).

Inductive pa_model' (s : heap) : Ptr -> (nat -> nat) -> nat -> Type :=
  | pa_model_array' :
     forall p, find s p = Some (dyn data Arr) -> pa_model' s p parray 0 
  | pa_model_diff' :
     forall p i v p', find s p = Some (dyn data (Diff i v p')) ->
                 forall f n, pa_model' s p' f n ->
                        pa_model' s p (upd f i v) (Coq.Init.Datatypes.S n).

Definition getSpec' : nat -> Ptr -> nat -> WhileL nat.
  intros n ptr i.
  refine (Spec _ _).
  refine (Predicate _ (fun s => { f : nat -> nat & pa_model' s ptr f n}) _).
  intros s [f H] v.
  refine (fun s' => prod (s = s') (v = f i)).
Defined.

Lemma getRefinement' : forall n ptr i, getSpec' n ptr i ⊑ get' n ptr i.
Proof.
  intros.
  unfold getSpec', get'.
  (* eapply readSpec. *)
Admitted.


(* A (non-executable) implementation fulfilling only partial-correctness *)

Definition get (ptr : Ptr) (i : nat) : WhileL nat := 
  Read _ data ptr
       (fun ptrVal => match ptrVal with
                       | Arr => Return _ (parray i)
                       | Diff j v ptr' =>
                         if beq_nat i j
                         then Return _ v
                         else getSpec ptr' i
                     end).

Lemma getRefinement : forall ptr i, getSpec ptr i ⊑ get ptr i.
Proof.
  intros.
  READ ptr vInPtr.
  inversion X0; subst; simpl in *; eauto.
  assert (Ha : forall (A : Type) (a b : A), Some a = Some b -> a = b) by
      (intros A a b HInv; now inversion HInv).
  assert (Ha1 : forall (A : Type) t1 t2, dyn A t1 = dyn A t2 -> t1 = t2) by
      (intros A t1 t2 HInv; inversion HInv; now apply inj_pair2 in H0).
  destruct vInPtr as [ | j v ptr' ]; simpl.
  (* Original persistent array *)
  - apply returnStep; unfold_refinements; refine_simpl.
    inversion X; subst; auto.
    simpl in *.
    rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
  (* Single modification of other persistent array *)
  - destruct (eq_nat_dec i j).
    + subst.
      rewrite <- beq_nat_refl.
      apply returnStep; unfold_refinements; refine_simpl.
      inversion X.
      subst; simpl in *.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      subst; simpl in *.
      unfold upd.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      subst; now rewrite <- beq_nat_refl.
    + rewrite <- PeanoNat.Nat.eqb_neq in n.
      rewrite n.
      unfold getSpec.
      refine (Refinement _ _ _ _).
      Unshelve. Focus 2.
      refine_simpl; auto.
      inversion X; simpl in *; subst.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      subst.
      exists f; auto.
      refine_simpl.
      admit. (* looks like it is related to X *)
      inversion X0; simpl in *; subst.
      clear X.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      rewrite e in H; apply Ha in H; apply Ha1 in H; inversion H.
      subst.
      unfold upd; rewrite n.
      admit. (* looks like it is related to X *)
Admitted.

(* attempt at defining recursion *)
Inductive WhileL' (a : Type) : Type :=
  | New'    : forall v, v -> (Ptr -> WhileL' a) -> WhileL' a
  | Read'   : forall v, Ptr -> (v -> WhileL' a) -> WhileL' a
  | Write'  : forall v, Ptr -> v -> WhileL' a  -> WhileL' a
  | While'  : (S -> Prop) -> (S -> bool) -> WhileL' unit -> WhileL' a -> WhileL' a
  | Spec'   : PT a -> WhileL' a
  | Fix     : forall (R : S -> a -> a -> Prop) s,
                well_founded (R s) ->
                (* ... -> *)
                WhileL' a
  | Return' : a -> WhileL' a.

(*
Parameter N : nat.

Inductive repr (f : nat -> nat) : nat -> nat -> Prop :=
  | repr_zero : forall i, f i = i -> repr f i i
  | repr_succ : forall i j r, f i = j -> 0 <= j < N -> ~ j = i -> repr f j r ->
                         repr f i r.

Definition reprf (f : nat -> nat) :=
  (forall i, 0 <= i < N -> 0 <= f i < N) /\
  (forall i, 0 <= i < N -> exists j, repr f i j).
*)




(* Attempt following Chargueraud's paper *)

Definition Rank := nat.

(* We know that Ptr will point to Content 
   TODO maybe find a better translation for polymorphic references "ref a"? *)
Definition Elem := Ptr.

Inductive Content : Type :=
  | Root : Rank -> Content
  | Link : Elem -> Content.

(** Make **)

Definition make : unit -> WhileL Elem :=
  fun _ => New _ _ 0 (fun ptr => Return _ ptr).

Definition makeSpec : WhileL Elem.
  refine (Spec _ _).
  refine (Predicate _ (fun s => True) _).
  intros s H t s'.
  refine ({p : Ptr | find s' p = Some (dyn Rank 0)}).
Defined.

Lemma makeResult : makeSpec ⊑ make tt.
Proof.
  NEW 0 p.
  apply returnStep.
  unfold_refinements; refine_simpl; exists p; auto.
Qed.

(** Find/Link **)

(* TODO the following 2 definitions should be used temporarly *)
Definition addr_eqb (x : Addr.addr) (y : Addr.addr) :=
  match x, y with
    | Addr.MkAddr v1, Addr.MkAddr v2 => Nat.eqb v1 v2
  end.

Definition eqb_addr_spec : forall x y, reflect (x = y) (addr_eqb x y).
  intros x y; destruct x; destruct y; simpl; apply iff_reflect; split; intros;
  [ inversion H; now apply PeanoNat.Nat.eqb_eq
  | apply f_equal; now apply PeanoNat.Nat.eqb_eq ].
Defined.

Definition linkByRank (x : Elem) (y : Elem) (rx : Rank) (ry : Rank) :
  WhileL Elem :=
  match Nat.compare rx ry with
    | Lt => Write _ _ x (Link y) (Return _ y)
    | Gt => Write _ _ y (Link x) (Return _ x)
    | Eq => Write _ _ y (Link x) (Write _ _ y (Root (Nat.succ rx)) (Return _ x))
  end.

Definition link (x : Elem) (y : Elem) : WhileL Elem :=
  if addr_eqb x y
  then Return _ x
  else let readPtrs k :=
           Read _ _ x (fun xVal => Read _ _ y (fun yVal => k xVal yVal)) in
       let cont (vx vy : Content) :=
           match vx, vy with
             | Root rx, Root ry => linkByRank x y rx ry
             | _, _ => Return _ x (* hopefully during the refinement process
                                     we can show this case will never occur *)
           end in
       readPtrs cont.

(* I don't like this spec, it's too similar to the code *)
Definition linkSpec (x : Elem) (y : Elem) : WhileL Elem.
  refine (Spec _ _).
  refine (Predicate _ (fun s => prod ({r : Rank | find s x =
                                                  Some (dyn Content (Root r))})
                                     ({r : Rank | find s y =
                                                  Some (dyn Content (Root r))}))
                    _).
  intros s [[rx HxFind] [ry HyFind]] t s'.
  destruct (eqb_addr_spec x y).
  apply (t = x).
  destruct (Nat.compare rx ry).
  apply (prod (find s' x = Some (dyn Content (Link y))) (t = y)).
  apply (prod (find s' y = Some (dyn Content (Link x))) (t = x)).
  apply (prod (find s' y = Some (dyn Content (Link x)))
              (prod (find s' x = Some (dyn Content (Root (Nat.succ rx))))
                    (t = y))).
Defined.

(* The following does not pass Coq's termination checker *)

Fixpoint ufind (x : Elem) : WhileL Elem.
(* The following does not pass Coq's termination checker
refine (
  Read Elem Content x
       (fun v => match v with
                  | Root _ => Return _ x
                  | Link y => bind (ufind y)
                                   (fun z => Write _ _ x (Link z) (Return _ z))
                end)). *)
Admitted.

(* TODO This accounts for paths but not for updated references *)
Inductive PathToRoot (s : heap) (el : Elem) : list Elem -> Type :=
  | This : forall v, find s el = Some (dyn Content (Root v)) ->
                PathToRoot s el (el :: nil)
  | Path : forall p r l, find s p = Some (dyn Content (Link r)) ->
                    PathToRoot s el l -> 
                    PathToRoot s el (r :: l).

Definition findSpec (x : Elem) : WhileL Elem.
  refine (Spec _ _).
  refine (Predicate _ (fun s => { v : Content | find s x = Some (dyn Content v)}) _).
  intros s [v HFindX] t s'.
  refine ({ l : list Elem & prod (PathToRoot s x l)
                                 (head (rev l) = Some t) } ).
Defined.

(** Union and Equiv **)

Definition union (x y : Elem) : WhileL Elem :=
  bind (ufind x) (fun xVal => bind (ufind y) (fun yVal => link xVal yVal)).

Definition equiv (x y : Elem) : WhileL bool :=
  bind (ufind x) (fun xVal => bind (ufind y)
                                  (fun yVal => Return _ (addr_eqb xVal yVal))).
  
(** End of example **)

Definition refineIf' {a} (cond : bool) (pt : PT a) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  (Spec a pt) ⊑ if cond then (Spec a thenBranch) else (Spec a elseBranch).
Proof.
  unfold_refinements; destruct cond; simpl;
  set (d := (fun s pres => pair pres I) : pre pt ⊂ pre ([fun s : S => (pre pt s * True)%type,
                                        fun (s : S) (pre : pre pt s * True) (s' : a) => post pt s (fst pre) s']));
  apply (Refinement _ _ d); intros; destruct_pt a; auto.
Defined.

Lemma refineWhilePT' {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) : 
  let pt := [inv , fun _ _ _ s' => inv s' /\ Q s'] in
  let body : PT a := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  (forall s, Is_false (cond s) /\ inv s -> Q s) ->
  pt ⊏ WhilePT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (WhilePT inv cond body)) by
      (refine_simpl; repeat split; destruct_conjs; auto).
    apply (Refinement _ _ d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.

(* TODO: update this to handle the continuation too
Lemma refineWhile {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) 
  (StrQ : forall s, Is_false (cond s) /\ inv s -> Q s) : 
  let w := Spec a ([inv , fun _ _ _ s' => inv s' /\ Q s']) in
  let body := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  w ⊑ While a inv cond (Spec a body).
  Proof.
    refine_simpl; now (apply refineWhilePT).
  Qed.
*)


(* Lemma newSpec {a b : Type} (spec : PT a) (w : Ptr -> WhileL a) (v : b) *)
(*       (H : forall s, pre spec s -> pre spec (update s (alloc s) (dyn b v))) *)
(*       (H1 : forall s x v' s0, *)
(*               post spec (update s (alloc s) (dyn b v)) (H s x) v' s0 -> *)
(*               post spec s x v' s0) *)
(*       (Step : forall p,  *)
(*                 Spec _ ([ fun s =>  *)
(*                             {t : S & prod (pre spec s)  *)
(*                                      (prod (s = update t p (dyn b v)) *)
(*                                            (p = alloc t)) *)
(*                                      } *)
(*                            , fun s pres v s' => post spec s (fst (projT2 pres)) v s' ]) ⊑ w p) : *)
(*   Spec _ spec ⊑ New _ b v w. *)
(* Proof. *)
(*   eapply newStep. Unshelve. Focus 2. *)
(*   * refine_simpl. *)
(*     exists (alloc s); split; [ apply allocFresh | ]. *)
(*     destruct (Step (alloc s)) as [d h]. *)
(*     apply d. *)
(*     destruct spec. *)
(*     refine_simpl. *)
(*     exists s. *)
(*     split. *)
(*     now apply H. *)
(*     split; [ now trivial | reflexivity]. *)
(*   * refine_simpl; destruct (Step (alloc s)) as [d h]; apply H1. *)
(*     destruct spec; simpl in *; apply h in X; now simpl in X. *)
(* Qed. *)




(* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
(* Definition swapResult (P : Ptr) (Q : Ptr) (D : P <> Q) (a : Type) : *)
(*   let SetQinN (s : Ptr -> WhileL unit) := *)
(*       (Read _ a Q) (fun v => New _ _ v s) in *)
(*   let SetPinQ (s : WhileL unit) := *)
(*       (Read _ a P) (fun v => Write _ _ Q v s) in *)
(*   let SetNinP (N : Ptr) (s : WhileL unit) := *)
(*       (Read _ a N) (fun v => Write _ _ P v s) in *)
(*   @SWAP a P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))). *)
(* Proof. *)
(*   intros. *)
(*   unfold SetQinN. *)
(*   eapply readSpec; refine_simpl. *)
(*   now exists s1. *)
(*   eapply newSpec. refine_simpl. *)
(*   rewrite <- H. *)
(*   rewrite findAlloc; auto. *)
(*   apply MFacts.in_find_iff; unfold not; intro HH; *)
(*   unfold find in H2; rewrite H2 in HH; inversion HH. *)
(*   rewrite <- H0. *)
(*   rewrite findNUpdate. *)
(*   reflexivity. *)
(*   eapply allocDiff. *)
(*   apply H1. *)
  
(*   intros T; eapply readSpec. *)
(*   refine_simpl. *)
(*   now exists s0. *)
(*   intro vInP. *)
(*   simpl. *)
(*   eapply writeSpec. *)
(*   refine_simpl; eauto. *)
(*   eapply readSpec. *)
(*   refine_simpl. *)
(*   exists v. *)
(*   rewrite findNUpdate. *)
(*   rewrite findUpdate. *)
(*   reflexivity. *)
(*   rewrite findAlloc in H. *)
(*   eapply (allocDiff' _ _ _ H). *)
(*   admit. *)
(*   refine_simpl. *)
(*   eapply writeSpec. *)
(*   refine_simpl; auto. *)
(*   exists vInP. *)
(*   rewrite findNUpdate; auto. *)
(*   apply returnStep; refine_simpl. *)
(*   unfold preConditionOf in pre; simpl in pre. *)
(*   destruct_conjs. *)
(*   simpl; subst. *)
(*   rewrite e2. *)
(*   rewrite findNUpdate; auto. *)
(*   unfold preConditionOf in *. *)
(*   simpl in *; subst. *)
(*   destruct_conjs. *)
(*   simpl. *)
(*   subst.  *)
(*   rewrite findUpdate. *)
(*   rewrite <- e0. *)
(*   rewrite findNUpdate. *)

  
(*   rewrite findNUpdate. *)
(*   assumption. *)
(*   admit.  *)
(* (* same admit as above *) *)
(*   Unshelve. *)
(*   refine_simpl. *)
(*   eapply heapGrows. *)
(*   apply H0. *)
(*   eapply heapGrows. *)
(*   apply e. *)
(*   rewrite findNUpdate. *)
(*   assumption. *)
(*   apply (allocDiff (dyn a v)); assumption. *)
(* Admitted.   *)
  
(* (** End of example **) *)



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

Section WHILE.
Definition Ptr := Addr.t.

Variable v : Type.

Inductive WhileL (a : Type) : Type :=
  | New    : v -> (Ptr -> WhileL a) -> WhileL a
  | Read   : Ptr -> (v -> WhileL a) -> WhileL a
  | Write  : Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S v -> Prop) -> (S v -> bool) -> WhileL unit -> WhileL a -> WhileL a
  | Spec   : PT v a -> WhileL a
  | Return : a -> WhileL a.

Notation "addr ≔ exp" := (Write id addr) (at level 52).

Fixpoint semantics {a : Type} (w: WhileL a) : PT v a :=
  match w with
    | New _ v k =>
      let pre := fun s => 
                  { ptr : Ptr & prod (find _ s ptr = None)
                              (pre _ (semantics (k ptr)) (update _ s ptr v)) } in 
      let post := fun s pres v' s' => 
                    post _ (semantics (k (projT1 pres))) (update _ s (projT1 pres) (v)) (snd (projT2 pres)) v' s' in
      
      Predicate _ _ pre post
    | Read _ ptr k =>
      let readPre := fun h => { x : v & find _ h ptr = Some x} in
      let pre := fun s => {p : readPre s & pre _ (semantics (k (projT1 p))) s} in
      let post := fun s pres x s' => 
                    post _ (semantics (k (projT1 (projT1 pres)))) s (projT2 pres) x s' in
      Predicate _ _ pre post
    | Write _ ptr x k => 
      let pre := fun s => 
                   prod ({y : v & find _ s ptr = Some y})
                        (pre _ (semantics k) (update _ s ptr x)) in
      let post := fun s pres res s' =>
                    post _ (semantics k) (update _ s ptr x) (snd pres) res s' in
      Predicate _ _ pre post
    | While _ inv c body k => SeqPT _ (WhilePT _ inv c (semantics body)) (@semantics a k)
    | Spec _ s => s
    | Return _ x => Predicate _ _ (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition preConditionOf {a : Type} (w : WhileL a) : Pow (S v) :=
  match semantics w with
    | Predicate _ _ p _ => p
  end.

Definition postConditionOf {a : Type} (w : WhileL a)
  : (forall s : (S v), preConditionOf w s -> a -> Pow (S v)) :=
  match semantics w as x return (forall s : (S v), match x with | Predicate _ _ p _ => p end s -> a -> Pow (S v)) with
    | Predicate _ _ pre post => post
  end.

Fixpoint bind {a b : Type} (w : WhileL a) (k : a -> WhileL b) {struct w} : WhileL b :=
  match w with
  | New _ v c  => New _ v (fun p => bind (c p) k)
  | Read _ p c => Read _ p (fun v => bind (c v) k)
  | Write  _ p v c => Write _ p v (bind c k)
  | While _ Inv cond body c => While _ Inv cond body (bind c k)
  | Spec _ pt => Spec _ (BindPT _ pt (fun x => semantics (k x)))
  | Return _ x => k x
  end.

Notation "a ; b" := (bind a (fun _ => b)) (at level 60).

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ _ k     => forall ptr, isExecutable (k ptr)
    | Read _ _ k    => forall v, isExecutable (k v)
    | Write _ _ _ w   => isExecutable w
    | While _ inv c b k => isExecutable b /\ isExecutable k
    | Spec _ pt       => False
    | Return _ a      => True
  end.

Definition wrefines {a : Type} (w1 w2 : WhileL a) := Refines v (semantics w1) (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity).


(*******************************************************************************
                   ****   Basic automation ****
*******************************************************************************)


Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.
Ltac refine_unfold := unfold pre, post, subset, bind in *.
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
  wrefines w1 w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold_refinements; now apply refineTransPT.
  Defined.

Definition refineRefl {a} (w : WhileL a) :
  w ⊑ w.
    unfold_refinements; apply refineReflPT.
  Defined.

(*******************************************************************************
                   ****   Refinement properties ****
*******************************************************************************)

Lemma newRefines {a : Type} (w : WhileL a) (w' : Ptr -> WhileL a)
  (y : v)
  (H : subset _ (pre _ (semantics w)) (pre _ (semantics (New _ y w'))))
  (Q : forall (s : S v) (x : pre _ (semantics w) s) (v' : a),
   subset _ (post _ (semantics (New _ y w')) s (H s x) v') (post _ (semantics w) s x v'))
  : w ⊑ New _ y w'.
Proof.
  exact (Refinement _ _ _ H Q).
Qed.  

Lemma readRefines {a : Type} (w : WhileL a) (w' : v -> WhileL a)
  (ptr : Ptr)
  (H : subset _ (pre _ (semantics w)) (pre _ (semantics (Read _ ptr w'))))
  (Q : forall s p x s', 
         post _ (semantics (w' (projT1 (projT1 (H s p))))) s (projT2 (H s p)) x s' 
         -> post _ (semantics w) s p x s')
  : w ⊑ Read _ ptr w'.
Proof.
  exact (Refinement _ _ _ H Q).
Qed.  

Lemma readSpec {a : Type} (ptr : Ptr)  (spec : PT v a) (w' : v -> WhileL a)
  (H : forall s, pre _ (spec) s -> {y : v & find _ s ptr = Some (y)})
  (Step : forall y, Spec _ (Predicate _ _ (fun s => prod (pre _ spec s)
                                                    (find _ s ptr = Some y))
                                      (fun s pres x s' => post _ spec s (fst pres) x s')) ⊑ w' y) :
  Spec _ spec ⊑ Read _ ptr w'.
Proof.
  unshelve eapply readRefines.
  * refine_simpl.
    assert (valid : {y : v & find _ s ptr = Some y}) by now apply H.
    exists valid.
    destruct valid as [x P]; destruct (Step x) as [d h].
    refine_simpl.
    destruct (semantics (w' x)).
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
    set (Ha := pair p A2 : (pre s * (find _ s ptr = Some (A1)))).
    pose (h s Ha x s').
    simpl in p2.
    apply p2.
    apply B.
Qed.


Lemma newSpec {a : Type} (y : v) (spec : PT v a) (w : Ptr -> WhileL a)
      (H : forall s, pre _ spec s -> pre _ spec (update _ s (alloc _ s) (y)))
      (Step : forall p,
                Spec _ (Predicate _ _ (fun s => { t : S v & prod (pre _ spec t)
                                            (prod (forall p', M.In p' t -> p' <> p)
                                                  (s = (update _ t p (y)))) })
                                      (fun s pres v s' => post _ spec (projT1 pres) (fst (projT2 pres)) v s')) ⊑ w p) :
  Spec _ spec ⊑ New _ y w.
Proof.
  unshelve eapply newRefines.
  * refine_simpl.
    exists (alloc _ s); split;
    destruct (Step (alloc _ s)) as [d h];
    [ apply allocFresh |
      apply d; destruct spec; simpl in * ].
    exists s.
    repeat split; auto.
    unfold not; intros p' HIn HEq; subst. apply (allocNotIn _ _ HIn).
  * refine_simpl.
    destruct spec.
    destruct (Step (alloc _ s)).
    destruct (semantics (w (alloc _ s))).
    simpl in *.
    apply s1 in X.
    now simpl in X.
Qed.

Lemma newStep {a : Type} (y : v) (spec : PT _ a) 
      (H : forall s, pre _ spec s -> pre _ spec (update _ s (alloc _ s) (y)))
      (Step : {w : (Ptr -> WhileL a) & forall (p : Ptr),
                Spec _ (Predicate _ _ (fun s => { t : S v & prod (pre _ spec t)
                                            (prod (forall p', M.In p' t -> p' <> p)
                                                  (s = (update _ t p (y)))) })
                        (fun s pres v s' => post _ spec (projT1 pres) (fst (projT2 pres)) v s')) ⊑ w p}) :
  {w : WhileL a & Spec _ spec ⊑ w}.
  Proof.
    destruct Step as [w S].
    exists (New _ y w).
    now eapply newSpec.
  Qed.

Lemma writeRefines {a : Type} (w w' : WhileL a) (ptr : Ptr) (y : v)
  (d : subset _ (pre _ (semantics w)) (pre _ (semantics (Write _ ptr y w')))) 
  (h : forall (s : S v)(p : pre _ (semantics w) s)  (x : a) (s' : S v), 
    post _ (semantics w') (update _ s ptr (y)) (snd (d s p)) x s' -> post _ (semantics w) s p x s')
  : w ⊑ Write _ ptr y w'.
  Proof.
    exact (Refinement _ _ _ d h).
  Qed.

Lemma writeSpec {a : Type} (ptr : Ptr) (y : v) (spec : PT _ a) (w : WhileL a)
  (H : forall s, pre _ spec s -> {x : v & find _ s ptr = Some (x)})
  (Step :  Spec _
    (Predicate _ _  (fun s => {t : S v & prod (pre _ spec t) (s = (update _ t ptr (y)))})
                    (fun s pres x s' => 
              (post _ spec (projT1 pres) (fst (projT2 pres)) x s'))) ⊑ w) :
  Spec _ spec ⊑ Write _ ptr y w.
Proof.
  destruct Step as [d h]; unshelve eapply writeRefines.
  * refine_simpl; destruct spec; [ now apply H | apply d; now exists s].
  * refine_simpl; destruct spec; destruct (semantics w); pose (h _ _ _ _ X).
    now trivial.
Qed.

Lemma writeStep {a : Type} (ptr : Ptr) (y : v) (spec : PT _  a) 
  (H : forall s, pre _ spec s -> {x : v & find _ s ptr = Some x})
  (Step :  
     {w : WhileL a & Spec _
    (Predicate _ _ (fun s => {t : S v & prod (pre _ spec t) (s = (update _ t ptr y))})
       (fun s pres x s' => 
              (post _ spec (projT1 pres) (fst (projT2 pres)) x s'))) ⊑ w}) :
  {w : WhileL a & Spec _ spec ⊑ w}.
  Proof.
    destruct Step as [w' A].
    exists (Write _ ptr y w').
    now apply writeSpec.
  Qed.


Lemma readStep {a : Type} (ptr : Ptr)  (spec : PT _ a) 
  (H : forall s, pre _ (spec) s -> {y : v & find _ s ptr = Some y})
  (Step : {w : v -> WhileL a &
            forall y, 
            Spec _ (Predicate _ _ (fun s => prod (pre _ spec s)
                                   (find _ s ptr = Some y))
                    (fun s pres x s' => post _ spec s (fst pres) x s' )) ⊑ w y}) :
  {w : WhileL a & Spec _ spec ⊑ w}.
Proof.
  destruct Step as [w A].
  exists (Read _ ptr w).
  now apply readSpec.
Qed.

Lemma returnStep {a : Type} (x : a) (w : WhileL a) 
  (H : forall (s : S v) (pre : preConditionOf w s), postConditionOf w s pre x s) : 
  w ⊑ Return a x.
Proof.
  unshelve eapply Refinement; refine_simpl; apply H.
Qed.

Lemma changeSpec {a : Type} (pt2 pt1 : PT _ a) (w : WhileL a)
  (d : subset _ (pre _ pt1) (pre _ pt2))
  (h : forall (s : S v) (x : pre _ pt1 s) y, subset _ (post _ pt2 s (d s x) y) (post _ pt1 s x y))
  (H : Spec _ pt2 ⊑ w) :
  Spec _ pt1 ⊑ w.
  Proof.
    eapply refineTrans; [ | apply H].
    exact (Refinement _ _ _ d h).
  Qed.



  
Definition refineIf {a} (cond : bool) (pt : PT _ a) :
  let branchPre (P : S v -> Prop) := fun s => prod (pre _ pt s) (P s) in
  let thenBranch := Predicate _ _ (branchPre (fun s => Is_true cond))
                                  (fun s pre s' => post _ pt s (fst pre) s')  in
  let elseBranch := Predicate _ _ (branchPre (fun s => Is_false cond))
                                  (fun s pre s' => post _ pt s (fst pre) s') in
  (Spec a pt) ⊑ if cond then (Spec a thenBranch) else (Spec a elseBranch).
Proof.
  unfold_refinements; destruct cond; simpl;
  set (d := (fun s pres => pair pres I) : 
              subset _ (pre _ pt) 
                     (pre _ (Predicate _ _ (fun s : S v => (pre _ pt s * True)%type)
                                         (fun (s : S v) (pre : pre _ pt s * True) (s' : a) => post _ pt s (fst pre) s')))).
  apply (Refinement _ _ _ d); intros; destruct_pts; auto.
  refine_simpl.
  destruct pt.
  assumption.
  refine_simpl.
  destruct pt.
Admitted.

Lemma refineWhilePT {a} (inv : S v -> Prop) (cond : S v -> bool) (Q : S v -> Prop) : 
  let pt := Predicate _ _ (inv) (fun _ _ _ s' => inv s' /\ Q s') in
  let body : PT _ a := Predicate _ _ (fun s => inv s /\ Is_true (cond s)) (fun _ _ _ s => inv s) in
  (forall s, Is_false (cond s) /\ inv s -> Q s) ->
  Refines _ pt (WhilePT _ inv cond body).
  Proof.
    intros pt body QH; simpl in *.
    assert (d: subset _ (pre _ pt) (pre _ (WhilePT _ inv cond body))) by
      (refine_simpl; repeat split; destruct_conjs; auto).
    apply (Refinement _ _ _ d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.
End WHILE.


(************************************************************

                             SWAP EXAMPLE

*************************************************************)

  

(** Just a brief example showing how the language currently looks like 
    Contains some testing definitions to be moved elsewhere once proven.
**)
Definition SWAP {a : Type} (p q : Ptr): WhileL a unit.
  refine (Spec _ _ _).
  refine (Predicate _ _ (fun s => prod {x : a | find _ s p = Some x} {y : a | find _ s q = Some y}) _).
  intros s H t s'.
  refine (find _ s p = find _ s' q /\ find _ s q = find _ s' p).
Defined.

Hint Resolve allocDiff1 allocDiff2 heapGrows someExists someExistsT someIn findAlloc1 findAlloc2 freshDiff1 freshDiff2 not_eq_sym.
Hint Resolve findUpdate findNUpdate1 findNUpdate2.
Hint Resolve allocFresh findAlloc1 findAlloc2.

Ltac refine_unfold := unfold pre, post, subset, bind in *.
Ltac refine_simpl := 
  refine_unfold; intros; simpl in *; destruct_conjs; 
  repeat split; repeat subst; simpl in *.
Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.

Ltac heap_simpl := try (rewrite findAlloc1, findAlloc2 in * || rewrite findUpdate in * || rewrite findNUpdate1 in * || rewrite findNUpdate2 in *).
Ltac goal_simpl :=  refine_simpl; heap_simpl; eauto.
Ltac READ ptr v := eapply (readSpec _ ptr); [ | intros v]; goal_simpl.
Ltac NEW v ptr := eapply (newSpec _ v);  [ | intros ptr]; goal_simpl.
Ltac WRITE ptr v := eapply (writeSpec _ ptr v); goal_simpl.
Ltac ASSERT P := unshelve eapply (changeSpec _ P); goal_simpl.
Ltac RETURN v := eapply (returnStep _ v); unfold_refinements; goal_simpl.

Notation "P1 ⊑ P2" := (wrefines _ P1 P2) (at level 90, no associativity).
(* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
Definition swapResult {a : Type} (P : Ptr) (Q : Ptr) (D : P <> Q) :
  {c : WhileL a unit & SWAP P Q ⊑ c}.
Proof.
  econstructor; unfold SWAP.
  READ Q x.
  NEW x T.
  READ P y. 
  WRITE Q y. 
  READ T z. 
  WRITE P z. 
  RETURN tt.
  eapply findNUpdate2; [ eauto | ].
  rewrite findUpdate.
  rewrite <- e2.
  apply findNUpdate1.
  apply n; eauto.
  trivial.
  trivial.
  rewrite <- e0.
  apply findNUpdate2.
  apply not_eq_sym.
  apply n.
  eauto.
  now rewrite findUpdate.
Qed.  

(*******************************************************************************
                ****  Union-Find refinement example ****
*******************************************************************************)

(* Attempt following "A Persistent Union-Find Data Structure" *)

Set Implicit Arguments.
Require Export Wf_nat.

Inductive data : Type :=
  | Arr : (nat -> nat) -> data
  | Diff : nat -> nat -> Ptr -> data
  | ResultGet : option nat -> data
  | ResultFind : Ptr -> nat -> data.

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
(* Not in use at the moment *)
(*
Inductive pa_valid (s : heap) : Ptr -> Type :=
  | array_pa_valid : forall l p, find s p = Some (dyn data (Arr l)) -> pa_valid s p
  | diff_pa_valid : forall p i v p', find s p = Some (dyn data (Diff i v p')) ->
                                pa_valid s p' ->
                                pa_valid s p.
*)

(* 
   pa_model states that, given a pointer "p", we either have: 
   1. p points to an array "Arr", with elements given by (Z -> Z)
   2. p points to different "Diff", which is a change of another valid array,
      in one position only, updating the other array in that position (using upd)
*)
Inductive pa_model (s : heap data) : Ptr -> (nat -> nat) -> Type :=
  | pa_model_array :
     forall p f, find _ s p = Some ((Arr f)) -> pa_model s p f
  | pa_model_diff :
     forall p i v p', find _ s p = Some (Diff i v p') ->
                   forall f, pa_model s p' f ->
                        pa_model s p (upd f i v).

(*
Lemma pa_model_pa_valid :
  forall m p f, pa_model m p f -> pa_valid m p.
Proof.
  induction 1.
  eapply array_pa_valid; eauto.
  apply diff_pa_valid with (i:=i) (v:=v) (p':=p'); auto.
Qed.
*)

(** SET **)

Definition newRef (x : data) : WhileL data Ptr :=
  New _ _ x (fun ptr => Return _ _ ptr).

(* The original set implementation (i.e. no path compression), 
presented in Page 3 *)
Definition set (t : Ptr) (i : nat) (v : nat) : WhileL data Ptr :=
  Read _ _ t (fun vInT =>
  match vInT with
  | Arr f => New _ _ (Arr (upd f i v))
                (fun (res : Ptr) => Write _ _ t (Diff i (f i) res) (Return _ _ res))
  | Diff _ _ _ => newRef (Diff i v t)
  | _ => Return _ _ t (* absurd! *)                      
  end).

Definition setSpec (ptr : Ptr) (i : nat) (v : nat) : WhileL data Ptr.
  refine (Spec _ _ _).
  refine (Predicate _ _ (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] newPtr s'.
  apply (prod (pa_model s' newPtr (upd f i v))
              (pa_model s' ptr f)).
Defined.

(** Auxiliary lemmas about pa_model / upd. Taken from puf.v. **)

Axiom upd_ext : forall f g : nat -> nat, (forall i, f i = g i) -> f = g.

Lemma upd_eq : forall f i j v, i = j -> upd f i v j = v.
Proof.
Admitted.

Lemma upd_eq_ext :
  forall f i v, f = upd (upd f i v) i (f i).
Proof.
Admitted.
  
(* Application of pa_model_diff when "f" does not directly read as an upd *)
Lemma pa_model_diff_2 :
  forall p : Ptr, forall i v p', forall f f' s,
  find _ s p = Some ((Diff i v p')) -> 
  pa_model s p' f' ->
  f = upd f' i v ->
  pa_model s p f. 
Proof.
Admitted.

(* Main separation lemma *)
Lemma pa_model_sep :
  forall s t f v t',
    ~ (M.In t' s) -> 
    pa_model s t f -> pa_model (update _ s t' v) t f.
Proof.
  intros.
  intros; generalize dependent t'.
  induction X; intros.
  - apply pa_model_array.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst.
    apply someIn in e; contradiction.
  - apply pa_model_diff with (p' := p'); auto.
    apply findNUpdate1; auto.
    unfold not; intros; subst.
    apply someIn in e; contradiction.
Qed.

Lemma pa_model_alloc :
  forall s t' f v, pa_model s t' f -> pa_model (update _ s (alloc _ s) v) t' f.
Proof.
  intros; apply pa_model_sep; auto; apply allocNotIn.
Qed.

(* Tactics copied from While Section. To be removed later. *)


(** set refinement **)

Lemma setRefinement : forall ptr i v, wrefines _ (setSpec ptr i v) (set ptr i v).
Proof.
  intros; unfold set, setSpec.
  READ ptr vInPtr.
  inversion X0; eauto.
  destruct vInPtr as [ f | j vInJ t' | | ].
  - NEW (Arr (upd f i v)) res.
    inversion X; subst; rewrite H in e; inversion e.
    subst; exists f; apply pa_model_array; eauto.
    WRITE ptr (Diff i (f i) res).
    RETURN res.
    inversion X; subst; rewrite H in e1; inversion e1.
    subst; clear e1.
    apply pa_model_array.
    erewrite findNUpdate1 with (x := Some (Arr (upd f i v))); auto.
    unfold not; intros; subst; apply someIn in H; apply n in H; now apply H.
    inversion X; subst; rewrite H in e1; inversion e1.
    subst; clear e1.
    apply pa_model_diff_2 with (i := i) (v := f i) (p := ptr) (p' := res)
                                       (f' := upd f i v); auto.
    apply pa_model_array; eauto.
    apply upd_eq_ext.
  - unfold newRef; NEW (Diff i v ptr) res.
    inversion X; subst; rewrite H in e; inversion e.
    subst; clear e.
    exists (upd f j vInJ).
    apply pa_model_diff with (p := ptr) (p' := t'); eauto.
    now apply pa_model_alloc.
    RETURN res.
    apply pa_model_diff with (p' := ptr); auto.
    apply someIn in e0; apply pa_model_sep; auto.
    unfold not; intros H; apply n in H; now apply H.
    apply someIn in e0; apply pa_model_sep; auto.
    unfold not; intros H; apply n in H; now apply H.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
Qed.

(*** GET ***)
(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
*)

Definition data_get_eqb_none (h : option data) : bool :=
  match h with
    | Some (ResultGet None) => true
    | _ => false
  end.

(*
Definition get (ptr : Ptr) : WhileL unit :=
  t <- ptr
  done <- newRef Nothing
  while done == Nothing  {
    x <- read t
    match x with
      | Array => write done Just (a.i)
      | Diff (j, v, t') => if i == j 
                           then write done (Just v) 
                           else read t' >>= \x -> write t x
  }
*)

Definition get (ptr : Ptr) (i : nat) : WhileL data nat. Print data.
refine (
  Read _ _ ptr (fun vInPtr =>
  New _ _ vInPtr (fun t =>
  New _ _ (ResultGet None) (fun done =>
  While _ _ (fun s => True)
        (fun s => data_get_eqb_none (find _ s done))
        (Read _ unit t (fun vInT => _ )) (* the body is refined below *)
        (Read _ nat done (fun vInDone =>
         match vInDone with
           | ResultGet (Some a) => Return _ _ a
           | _ => Return _ _ 0 (* absurd *)
         end)))))).
(* body of the loop *)
destruct vInT as [ f | j v t' | | ].
refine (Write _ _ done (ResultGet (Some (f i))) (Return _ _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write _ _ done (ResultGet (Some v)) (Return _ _ tt)).
refine (Read _ _ t' (fun vInT' => Write _ _ t vInT' (Return _ _ tt))).
refine (Return _ _ tt). (* absurd: t will never point to a result *)
refine (Return _ _ tt). (* absurd: t will never point to a result *)
Defined.

(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
 *)
Definition getSpec : Ptr -> nat -> WhileL data nat.
  intros ptr i.
  refine (Spec _ _ _). 
  refine (Predicate _ _ (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] v.
  refine (fun s' => prod (s = s') (v = f i)).
Defined.

Hint Constructors pa_model.
Hint Resolve pa_model_alloc pa_model_sep.

Lemma getRefinement :  forall ptr i, wrefines _ (getSpec ptr i) (get ptr i).
Proof.
  intros.
  unfold get.
  (* READ *)
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  (* NEW *)
  NEW vInPtr t.
  apply newSpec; [ | intros done]; simpl; intros. (* ; goal_simpl. *)
  destruct_conjs; subst.
  exists X; repeat split; eauto.
  admit. (* this should be provable using heap lemmas *)
  admit. (* while rule needed here *)
Admitted.

(** FIND **)

Inductive dataUF :=
  | Rank : dataUF
  | Parent : dataUF.

Parameter N : nat.

Inductive repr (f : nat -> nat) : nat -> nat -> Prop :=
  | repr_zero : forall i, f i = i -> repr f i i
  | repr_succ : forall i j r, f i = j -> 0 <= j < N -> ~ j = i -> repr f j r ->
                         repr f i r.

Definition reprf (f : nat -> nat) :=
  (forall i, 0 <= i < N -> 0 <= f i < N) /\
  (forall i, 0 <= i < N -> exists j, repr f i j).

(*
let rec find_aux f i =
  let fi = A.get f i in
  if fi == i then
    f, i
  else
    let f, r = find_aux f fi in
    let f = A.set f i r in
    f, r
*)

(*
let find_aux_loop f i =
  ref ptr <- f
  ref refi <- i
  result <- none
  while result == none
    n <- refi
    fi <- A.get ptr n
    if (fi == i)
    then fi
    else A.set f i r

*)

Definition find_aux (f : Ptr) (i : nat) : WhileL data (prod Ptr nat).
  refine(
      let fi := get f i in
      bind _ fi (fun rfi => if Nat.eqb rfi i
                           then Return _ _ (f,i)
                           else _)).
Admitted.
  
  
(** UNION **)

(*
let union m i j =
  let ri = find m i in
  let rj = find m j in
  if ri <> rj then M.add ri rj m else m
*)
  

(** STOP HERE **)

(* A (non-executable) implementation fulfilling only partial-correctness *)

Definition get' (ptr : Ptr) (i : nat) : WhileL data nat := 
  Read _ _ ptr
       (fun ptrVal => match ptrVal with
                       | Arr f => Return _ _ (f i)
                       | Diff j v ptr' =>
                         if beq_nat i j
                         then Return _ _ v
                         else getSpec ptr' i
                       | _ => Return _ _ 0 (* absurd *)
                     end).

Lemma getRefinement' : forall ptr i, getSpec ptr i ⊑ get' ptr i.
Proof.
  intros.
  READ ptr vInPtr.
  inversion X0; subst; simpl in *; eauto.
  destruct vInPtr as [ | j v ptr' | | ]; simpl.
  (* Original persistent array *)
  - apply returnStep; unfold_refinements; refine_simpl.
    inversion X; subst; rewrite H in e; now inversion e.
  (* Single modification of other persistent array *)
  - destruct (eq_nat_dec i j).
    + subst.
      rewrite <- beq_nat_refl.
      apply returnStep; unfold_refinements; refine_simpl.
      inversion X; subst; simpl in *.
      rewrite e in H; inversion H.
      unfold upd.
      rewrite H in e; inversion e; subst; clear e.
      now rewrite <- beq_nat_refl.
    + rewrite <- PeanoNat.Nat.eqb_neq in n.
      rewrite n.
      unfold getSpec.
      refine (Refinement _ _ _ _ _).
      Unshelve. Focus 2.
      refine_simpl; auto.
      inversion X; simpl in *; subst.
      rewrite e in H; inversion H.
      rewrite H in e; inversion e; subst; clear e.
      exists f; auto.
      refine_simpl.
      admit. (* looks like it is related to X *)
      inversion X0; simpl in *; subst.
      clear X.
      rewrite H in e; inversion e.
      rewrite e in H; inversion H; subst.
      unfold upd; rewrite n.
      admit. (* looks like it is related to X *)
  - RETURN 0; inversion X; rewrite e in H; inversion H.
  - RETURN 0; inversion X; rewrite e in H; inversion H.
Admitted.

(* attempt at defining recursion *)
Inductive WhileL' (I : Type) (O : I -> Type) (a : Type) : Type :=
  | New'    : forall v, v -> (Ptr -> WhileL' O a) -> WhileL' O a
  | Read'   : forall v, Ptr -> (v -> WhileL' O a) -> WhileL' O a
  | Write'  : forall v, Ptr -> v -> WhileL' O a  -> WhileL' O a
  | Spec'   : forall v, PT v a -> WhileL' O a
  | Call    : forall (i : I), (O i -> WhileL' O a) -> WhileL' O a
  | Return' : a -> WhileL' O a.

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



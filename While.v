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

Set Implicit Arguments.

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

Fixpoint semantics {a : Type} (w: WhileL a) : PT v a :=
  match w with
    | New v k =>
      let pre := fun s => 
                  { ptr : Ptr & prod (find s ptr = None)
                              (pre (semantics (k ptr)) (update s ptr v)) } in 
      let post := fun s pres v' s' => 
                    post (semantics (k (projT1 pres))) (update s (projT1 pres) (v)) (snd (projT2 pres)) v' s' in
      
      Predicate pre post
    | Read ptr k =>
      let readPre := fun h => { x : v & find h ptr = Some x} in
      let pre := fun s => {p : readPre s & pre (semantics (k (projT1 p))) s} in
      let post := fun s pres x s' => 
                    post (semantics (k (projT1 (projT1 pres)))) s (projT2 pres) x s' in
      Predicate pre post
    | Write ptr x k => 
      let pre := fun s => 
                   prod ({y : v & find s ptr = Some y})
                        (pre (semantics k) (update s ptr x)) in
      let post := fun s pres res s' =>
                    post (semantics k) (update s ptr x) (snd pres) res s' in
      Predicate pre post
    | While inv c body k => SeqPT (WhilePT inv c (semantics body)) (@semantics a k)
    | Spec s => s
    | Return  x => Predicate (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition preConditionOf {a : Type} (w : WhileL a) : Pow (S v) :=
  match semantics w with
    | Predicate p _ => p
  end.

Definition postConditionOf {a : Type} (w : WhileL a)
  : (forall s : (S v), preConditionOf w s -> a -> Pow (S v)) :=
  match semantics w as x return (forall s : (S v), match x with | Predicate p _ => p end s -> a -> Pow (S v)) with
    | Predicate pre post => post
  end.

Fixpoint bind {a b : Type} (w : WhileL a) (k : a -> WhileL b) {struct w} : WhileL b :=
  match w with
  | New v c  => New v (fun p => bind (c p) k)
  | Read p c => Read p (fun v => bind (c v) k)
  | Write p v c => Write p v (bind c k)
  | While Inv cond body c => While Inv cond body (bind c k)
  | Spec pt => Spec (BindPT pt (fun x => semantics (k x)))
  | Return x => k x
  end.

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ k     => forall ptr, isExecutable (k ptr)
    | Read _ k    => forall v, isExecutable (k v)
    | Write _ _ w   => isExecutable w
    | While inv c b k => isExecutable b /\ isExecutable k
    | Spec pt       => False
    | Return a      => True
  end.

Definition wrefines {a : Type} (w1 w2 : WhileL a) := Refines (semantics w1) (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity).


(*******************************************************************************
                   ****   Basic automation ****
*******************************************************************************)


Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.
Ltac refine_unfold := unfold pre, post, subset, bind in *.
Ltac refine_simpl := 
  refine_unfold; intros; simpl in *; destruct_conjs; 
  repeat split; repeat subst; simpl in *.


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
  (H : subset (pre (semantics w)) (pre (semantics (New y w'))))
  (Q : forall (s : S v) (x : pre (semantics w) s) (v' : a),
   subset (post (semantics (New y w')) s (H s x) v') (post (semantics w) s x v'))
  : w ⊑ New y w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma readRefines {a : Type} (w : WhileL a) (w' : v -> WhileL a)
  (ptr : Ptr)
  (H : subset (pre (semantics w)) (pre (semantics (Read ptr w'))))
  (Q : forall s p x s', 
         post (semantics (w' (projT1 (projT1 (H s p))))) s (projT2 (H s p)) x s' 
         -> post (semantics w) s p x s')
  : w ⊑ Read ptr w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma readSpec {a : Type} (ptr : Ptr)  (spec : PT v a) (w' : v -> WhileL a)
  (H : forall s, pre (spec) s -> {y : v & find s ptr = Some (y)})
  (Step : forall y, Spec (Predicate (fun s => prod (pre spec s)
                                                    (find s ptr = Some y))
                                      (fun s pres x s' => post spec s (fst pres) x s')) ⊑ w' y) :
  Spec spec ⊑ Read ptr w'.
Proof.
  unshelve eapply readRefines.
  * refine_simpl.
    assert (valid : {y : v & find s ptr = Some y}) by now apply H.
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
    set (Ha := pair p A2 : (pre s * (find s ptr = Some (A1)))).
    pose (h s Ha x s').
    simpl in p2.
    apply p2.
    apply B.
Qed.


Lemma newSpec {a : Type} (y : v) (spec : PT v a) (w : Ptr -> WhileL a)
      (H : forall s, pre spec s -> pre spec (update s (alloc s) (y)))
      (Step : forall p,
                Spec (Predicate (fun s => { t : S v & prod (pre spec t)
                                            (prod (forall p' x, find t p' = Some x -> p' <> p)
                                                  (s = (update t p (y)))) })
                                      (fun s pres v s' => post spec (projT1 pres) (fst (projT2 pres)) v s')) ⊑ w p) :
  Spec spec ⊑ New y w.
Proof.
  unshelve eapply newRefines.
  * refine_simpl.
    exists (alloc s); split;
    destruct (Step (alloc s)) as [d h];
    [ apply allocFresh |
      apply d; destruct spec; simpl in * ].
    exists s.
    repeat split; auto.
    unfold not; intros p' HIn HEq; subst.
    apply (allocDiff1 _ HEq).
  * refine_simpl.
    destruct spec.
    destruct (Step (alloc s)).
    destruct (semantics (w (alloc s))).
    simpl in *.
    apply s1 in X.
    now simpl in X.
Qed.

Lemma newStep {a : Type} (y : v) (spec : PT _ a) 
      (H : forall s, pre spec s -> pre spec (update s (alloc s) (y)))
      (Step : {w : (Ptr -> WhileL a) & forall (p : Ptr),
                Spec (Predicate (fun s => { t : S v & prod (pre spec t)
                                            (prod (forall p' x, find t p' = Some x -> p' <> p)
                                                  (s = (update t p (y)))) })
                        (fun s pres v s' => post spec (projT1 pres) (fst (projT2 pres)) v s')) ⊑ w p}) :
  {w : WhileL a & Spec spec ⊑ w}.
  Proof.
    destruct Step as [w S].
    exists (New y w).
    now eapply newSpec.
  Qed.

Lemma writeRefines {a : Type} (w w' : WhileL a) (ptr : Ptr) (y : v)
  (d : subset (pre (semantics w)) (pre (semantics (Write ptr y w')))) 
  (h : forall (s : S v)(p : pre (semantics w) s)  (x : a) (s' : S v), 
    post (semantics w') (update s ptr (y)) (snd (d s p)) x s' -> post (semantics w) s p x s')
  : w ⊑ Write ptr y w'.
  Proof.
    exact (Refinement _ _ d h).
  Qed.

Lemma writeSpec {a : Type} (ptr : Ptr) (y : v) (spec : PT _ a) (w : WhileL a)
  (H : forall s, pre spec s -> {x : v & find s ptr = Some (x)})
  (Step :  Spec
    (Predicate  (fun s => {t : S v & prod (pre spec t) (s = (update t ptr (y)))})
                    (fun s pres x s' => 
              (post spec (projT1 pres) (fst (projT2 pres)) x s'))) ⊑ w) :
  Spec spec ⊑ Write ptr y w.
Proof.
  destruct Step as [d h]; unshelve eapply writeRefines.
  * refine_simpl; destruct spec; [ now apply H | apply d; now exists s].
  * refine_simpl; destruct spec; destruct (semantics w); pose (h _ _ _ _ X).
    now trivial.
Qed.

Lemma writeStep {a : Type} (ptr : Ptr) (y : v) (spec : PT _ a) 
  (H : forall s, pre spec s -> {x : v & find s ptr = Some x})
  (Step :  
     {w : WhileL a & Spec
    (Predicate (fun s => {t : S v & prod (pre spec t) (s = (update t ptr y))})
       (fun s pres x s' => 
              (post spec (projT1 pres) (fst (projT2 pres)) x s'))) ⊑ w}) :
  {w : WhileL a & Spec spec ⊑ w}.
  Proof.
    destruct Step as [w' A].
    exists (Write ptr y w').
    now apply writeSpec.
  Qed.


Lemma readStep {a : Type} (ptr : Ptr)  (spec : PT _ a) 
  (H : forall s, pre (spec) s -> {y : v & find s ptr = Some y})
  (Step : {w : v -> WhileL a &
            forall y, 
            Spec (Predicate (fun s => prod (pre spec s)
                                   (find s ptr = Some y))
                    (fun s pres x s' => post spec s (fst pres) x s' )) ⊑ w y}) :
  {w : WhileL a & Spec spec ⊑ w}.
Proof.
  destruct Step as [w A].
  exists (Read ptr w).
  now apply readSpec.
Qed.

Lemma returnStep {a : Type} (x : a) (w : WhileL a) 
  (H : forall (s : S v) (pre : preConditionOf w s), postConditionOf w s pre x s) : 
  w ⊑ Return x.
Proof.
  unshelve eapply Refinement; refine_simpl; apply H.
Qed.

Lemma changeSpec {a : Type} (pt2 pt1 : PT _ a) (w : WhileL a)
  (d : subset (pre pt1) (pre pt2))
  (h : forall (s : S v) (x : pre pt1 s) y, subset (post pt2 s (d s x) y) (post pt1 s x y))
  (H : Spec pt2 ⊑ w) :
  Spec pt1 ⊑ w.
  Proof.
    eapply refineTrans; [ | apply H].
    exact (Refinement _ _ d h).
  Qed.

Definition refineIf {a} (cond : bool) (pt : PT _ a) :
  let branchPre (P : S v -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := Predicate (branchPre (fun s => Is_true cond))
                                  (fun s pre s' => post pt s (fst pre) s')  in
  let elseBranch := Predicate (branchPre (fun s => Is_false cond))
                                  (fun s pre s' => post pt s (fst pre) s') in
  (Spec pt) ⊑ if cond then (Spec thenBranch) else (Spec elseBranch).
Proof.
  unfold_refinements; destruct cond; simpl;
  set (d := (fun s pres => pair pres I) : 
              subset (pre pt) 
                     (pre (Predicate (fun s : S v => (pre pt s * True)%type)
                                         (fun (s : S v) (pre : pre pt s * True) (s' : a) => post pt s (fst pre) s')))).
  apply (Refinement _ _ d); intros; destruct pt; auto.
  refine_simpl.
  assumption.
  refine_simpl.
  destruct pt.
Admitted.

Lemma refineWhilePT {a} (inv : S v -> Prop) (cond : S v -> bool) (Q : S v -> Prop) : 
  let pt := Predicate (inv) (fun s _ _ s' => inv s' /\ Q s') in
  let body : PT _ a := Predicate (fun s => inv s /\ Is_true (cond s)) (fun _ _ _ s' => inv s') in
  (forall s, Is_false (cond s) /\ inv s -> Q s) ->
  Refines pt (WhilePT inv cond body).
  Proof.
    intros pt body QH; simpl in *.
    assert (d: subset (pre pt) (pre (WhilePT inv cond body))) by
      (refine_simpl; repeat split; destruct_conjs; auto).
    apply (Refinement _ _ d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.
End WHILE.

(************************************************************

                             TACTICS

*************************************************************)


Hint Resolve allocDiff1 allocDiff2 heapGrows someExists someExistsT someIn findAlloc1 findAlloc2 freshDiff1 freshDiff2 not_eq_sym.
Hint Resolve findUpdate findNUpdate1 findNUpdate2.
Hint Resolve allocFresh findAlloc1 findAlloc2.

Hint Rewrite findUpdate findNUpdate : Heap.

(* Simple tactics *)
Ltac refine_unfold := unfold pre, post, subset, bind in *.
Ltac refine_simpl := 
  refine_unfold; intros; simpl in *; destruct_conjs; 
  repeat split; repeat subst; simpl in *.
Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.

Ltac goal_simpl :=  refine_simpl; eauto.
Ltac context_simpl :=
  repeat match goal with
           | [H1 : find ?s ?T = Some ?x, H2 : find ?s ?T = Some ?y |- _ ] => assert (E : x = y) by (eapply (findUnique _ _ H1 H2)); subst x; clear H2
           | [H1 : find (update ?s ?X ?x) ?X = Some ?y |- _] => rewrite findUpdate in H1  
           | [H1 : find (update ?s ?X ?x) ?Y = Some ?y, H2 : ?Y <> ?X |- _] => rewrite (findNUpdate H2) in H1
         end.
  
Ltac context_clean :=
  repeat match goal with
           | [ H : Some ?x = Some ?x |- _] => clear H
           | [H : Some ?x = Some ?y |- _] => inversion H; subst
         end.

Ltac assert_diff P Q :=
  match goal with
      | [H1 : find ?s Q = Some ?Y, H2 : forall X Y, find ?s X = Some Y -> X <> P |- _] => assert (Q <> P) by (apply (H2 _ _ H1))
      | [H1 : find ?s P = Some ?Y, H2 : forall X Y, find ?s X = Some Y -> X <> Q |- _] => assert (P <> Q) by (apply (H2 _ _ H1))
  end.
                
Ltac simpl_lookup :=
  repeat match goal with
     | [H : ?Q <> ?T |- find ?s ?P = find (update ?s' ?T ?x) ?Q ] => rewrite findNUpdate; [ | eauto]
     | [H : ?T <> ?Q |- find ?s ?P = find (update ?s' ?T ?x) ?Q ] => rewrite findNUpdate; [ | eauto]
     | [ |- find ?s ?P = find (update ?s' ?Q ?x) ?Q ] => rewrite findUpdate
  end.
        
(* Tactics that apply certain constructs *)
Ltac READ ptr v := eapply (readSpec ptr); [ | intros v]; goal_simpl.
Ltac NEW v ptr := eapply (@newSpec _ _ v);  [ | intros ptr]; goal_simpl.
Ltac WRITE ptr v := eapply (@writeSpec _ _ ptr v); goal_simpl.
Ltac ASSERT P := unshelve eapply (changeSpec P); goal_simpl.
Ltac RETURN v := eapply (returnStep v); unfold_refinements; goal_simpl; context_simpl; context_clean.

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity).

(************************************************************

                             SWAP EXAMPLE

*************************************************************)

(** Just a brief example showing how the language currently looks like 
    Contains some testing definitions to be moved elsewhere once proven.
**)
Definition SWAP {a : Type} (p q : Ptr): WhileL a unit := 
  Spec (Predicate
          (fun s => prod {x : a | find s p = Some x} {y : a | find s q = Some y})
          (fun s _ _ s' => find s p = find s' q /\ find s q = find s' p)).

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
  assert (T <> Q) by eauto.
  assert (P <> T) by eauto.
  context_simpl; context_clean.
  now simpl_lookup.
  assert (T <> Q) by eauto.
  assert (P <> T) by eauto.
  context_simpl; context_clean.
  now simpl_lookup.
Qed.  

(*******************************************************************************
                ****  Union-Find refinement example ****
*******************************************************************************)

(* Attempt following "A Persistent Union-Find Data Structure" *)


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
     forall p f, find s p = Some ((Arr f)) -> pa_model s p f
  | pa_model_diff :
     forall p i v p', find s p = Some (Diff i v p') ->
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
  New x (fun ptr => Return _ ptr).

(* The original set implementation (i.e. no path compression), 
presented in Page 3 *)
Definition set (t : Ptr) (i : nat) (v : nat) : WhileL data Ptr :=
  Read t (fun vInT =>
  match vInT with
  | Arr f => New (Arr (upd f i v))
                (fun (res : Ptr) => Write t (Diff i (f i) res) (Return _ res))
  | Diff _ _ _ => newRef (Diff i v t)
  end).

Definition setSpec (ptr : Ptr) (i : nat) (v : nat) : WhileL data Ptr.
  refine (Spec _).
  refine (Predicate (fun s => { f : nat -> nat & pa_model s ptr f}) _).
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
  find s p = Some ((Diff i v p')) -> 
  pa_model s p' f' ->
  f = upd f' i v ->
  pa_model s p f. 
Proof.
Admitted.

(* Main separation lemma *)
Lemma pa_model_sep :
  forall s t f v t',
    ~ (M.In t' s) -> 
    pa_model s t f -> pa_model (update s t' v) t f.
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
  forall s t' f v, pa_model s t' f -> pa_model (update s (alloc s) v) t' f.
Proof.
  intros; apply pa_model_sep; auto; apply allocNotIn.
Qed.

(* Tactics copied from While Section. To be removed later. *)


(** set refinement **)

Lemma setRefinement : forall ptr i v, wrefines (setSpec ptr i v) (set ptr i v).
Proof.
  intros; unfold set, setSpec.
  (* READ ptr vInPtr. *)
  apply readSpec; [ | intros vInPtr]; goal_simpl.
  inversion X0; eauto.
  destruct vInPtr as [ f | j vInJ t' ].
  - apply newSpec; [ | intros res]; goal_simpl.
    (* NEW (Arr (upd f i v)) res. *)
    inversion X; subst.
    rewrite e in H; inversion H; symmetry in H; subst.
    exists s0.
    apply pa_model_array.
    rewrite findAlloc1; auto.
    now apply someIn in e.
    rewrite e in H; inversion H.
    eapply writeSpec.
    refine_simpl. eauto.
    (* inversion X0; subst. *)
    (* rewrite e0 in H; inversion H; symmetry in H1; subst; clear H. *)
    (* exists (Arr f). *)
    (* rewrite findNUpdate1 with (x := Some (Arr f)); auto. *)
    (* apply n. *)
    (* now apply someIn in e0. *)
    (* rewrite e0 in H; inversion H. *)
    (* RETURN. *)
    apply returnStep; unfold_refinements; goal_simpl.
    inversion X; subst.
    rewrite e1 in H; inversion H; subst; clear H.
    apply pa_model_array.
    erewrite findNUpdate1 with (x := Some (Arr (upd s1 i v))); auto.
    intros E; subst res.
    eapply (n _ _ e1 _).
    rewrite e1 in H; inversion H.
    inversion X; subst.
    rewrite e1 in H; inversion H; symmetry in H1; subst; clear H.
    apply pa_model_diff_2 with (i := i) (v := f i) (p := ptr) (p' := res)
                                       (f' := upd f i v); auto.
    apply pa_model_array.
    apply findNUpdate1.
    assert_diff res ptr; eauto.
    apply findUpdate.
    apply upd_eq_ext.
    rewrite e1 in H; inversion H.
  - unfold newRef.
    apply newSpec; [ | intros res]; goal_simpl.
    (* NEW (Diff i v ptr) res. *)
    inversion X; subst.
    rewrite e in H; inversion H.
    rewrite e in H; symmetry in H; inversion H; subst; clear H.
    exists (upd f j vInJ).
    apply pa_model_diff with (p := ptr) (p' := t').
    rewrite findAlloc1; auto.
    now apply someIn in e.
    now apply pa_model_alloc.
    (* RETURN. *)
    RETURN res.
    apply pa_model_diff with (p' := ptr).
    now rewrite findUpdate.
Admitted.    

(*** GET ***)
(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
*)

Definition get (ptr : Ptr) (i : nat) : WhileL nat.
refine (
  Read data ptr (fun vInPtr =>
  New data vInPtr (fun t =>
  New (option nat) None (fun done =>
      While (fun s => True)
              (fun s => ) (* find s done Nat.eqb (dyn None) *)
              (Read data t (fun vInT => ))
              (Read (option nat) done
                    (fun vInDone => match vInDone with
                                     | None => Return 0 (* absurd *)
                                     | Some a => Return a
                                   end)))))).
admit. (* TODO how do to defined boolean equality on dynamic *)
destruct vInT as [ f | j v t' ].
refine (Write done (Some (f i)) (Return tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (Some v) (Return tt)).
refine (Read data t' (fun vInT' => Write (option data) done (Some vInT')
                                          (Return tt))).
Admitted.

Definition getSpec : Ptr -> nat -> WhileL nat.
  intros ptr i.
  refine (Spec _).
  refine (Predicate (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] v.
  refine (fun s' => prod (s = s') (v = f i)).
Defined.

(** STOP HERE **)

    
Fixpoint get' (n : nat) (ptr : Ptr) (i : nat) : WhileL nat := 
  Read data ptr
       (fun ptrVal => match n, ptrVal with
                       | 0, Arr => Return (parray i)
                       | Coq.Init.Datatypes.S n', Diff j v ptr' =>
                         if beq_nat i j
                         then Return v
                         else get' n' ptr' i
                       | _,=> Return (parray i) (* absurd *)
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
  refine (Spec _).
  refine (Predicate (fun s => { f : nat -> nat & pa_model' s ptr f n}) _).
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
  Read data ptr
       (fun ptrVal => match ptrVal with
                       | Arr => Return (parray i)
                       | Diff j v ptr' =>
                         if beq_nat i j
                         then Return v
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
      refine (Refinement _).
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
Inductive WhileL' (I : Type) (O : I -> Type) (a : Type) : Type :=
  | New'    : forall v, v -> (Ptr -> WhileL' O a) -> WhileL' O a
  | Read'   : forall v, Ptr -> (v -> WhileL' O a) -> WhileL' O a
  | Write'  : forall v, Ptr -> v -> WhileL' O a  -> WhileL' O a
  | Spec'   : PT a -> WhileL' O a
  | Call    : forall (i : I), (O i -> WhileL' O a) -> WhileL' O a
  | Return' : a -> WhileL' O a.


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
  fun => New 0 (fun ptr => Return ptr).

Definition makeSpec : WhileL Elem.
  refine (Spec _).
  refine (Predicate (fun s => True) _).
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
    | Lt => Write x (Link y) (Return y)
    | Gt => Write y (Link x) (Return x)
    | Eq => Write y (Link x) (Write y (Root (Nat.succ rx)) (Return x))
  end.

Definition link (x : Elem) (y : Elem) : WhileL Elem :=
  if addr_eqb x y
  then Return x
  else let readPtrs k :=
           Read x (fun xVal => Read y (fun yVal => k xVal yVal)) in
       let cont (vx vy : Content) :=
           match vx, vy with
             | Root rx, Root ry => linkByRank x y rx ry
             | _, => Return x (* hopefully during the refinement process
                                     we can show this case will never occur *)
           end in
       readPtrs cont.

(* I don't like this spec, it's too similar to the code *)
Definition linkSpec (x : Elem) (y : Elem) : WhileL Elem.
  refine (Spec _).
  refine (Predicate (fun s => prod ({r : Rank | find s x =
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
                  | Root => Return x
                  | Link y => bind (ufind y)
                                   (fun z => Write x (Link z) (Return z))
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
  refine (Spec _).
  refine (Predicate (fun s => { v : Content | find s x = Some (dyn Content v)}) _).
  intros s [v HFindX] t s'.
  refine ({ l : list Elem & prod (PathToRoot s x l)
                                 (head (rev l) = Some t) } ).
Defined.

(** Union and Equiv **)

Definition union (x y : Elem) : WhileL Elem :=
  bind (ufind x) (fun xVal => bind (ufind y) (fun yVal => link xVal yVal)).

Definition equiv (x y : Elem) : WhileL bool :=
  bind (ufind x) (fun xVal => bind (ufind y)
                                  (fun yVal => Return (addr_eqb xVal yVal))).
  
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
  apply (Refinement d); intros; destruct_pt a; auto.
Defined.

Lemma refineWhilePT' {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) : 
  let pt := [inv , fun s' => inv s' /\ Q s'] in
  let body : PT a := [fun s => inv s /\ Is_true (cond s), (fun s => inv s)] in
  (forall s, Is_false (cond s) /\ inv s -> Q s) ->
  pt ⊏ WhilePT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (WhilePT inv cond body)) by
      (refine_simpl; repeat split; destruct_conjs; auto).
    apply (Refinement d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.

(* TODO: update this to handle the continuation too
Lemma refineWhile {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) 
  (StrQ : forall s, Is_false (cond s) /\ inv s -> Q s) : 
  let w := Spec a ([inv , fun s' => inv s' /\ Q s']) in
  let body := [fun s => inv s /\ Is_true (cond s), (fun s => inv s)] in
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
(*                 Spec ([ fun s =>  *)
(*                             {t : S & prod (pre spec s)  *)
(*                                      (prod (s = update t p (dyn b v)) *)
(*                                            (p = alloc t)) *)
(*                                      } *)
(*                            , fun s pres v s' => post spec s (fst (projT2 pres)) v s' ]) ⊑ w p) : *)
(*   Spec spec ⊑ New b v w. *)
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
(*       (Read a Q) (fun v => New v s) in *)
(*   let SetPinQ (s : WhileL unit) := *)
(*       (Read a P) (fun v => Write Q v s) in *)
(*   let SetNinP (N : Ptr) (s : WhileL unit) := *)
(*       (Read a N) (fun v => Write P v s) in *)
(*   @SWAP a P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return tt))). *)
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
(*   eapply (allocDiff' H). *)
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



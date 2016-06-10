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
  | While  : (S -> Prop) -> (S -> bool) -> WhileL a -> WhileL a -> WhileL a
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "addr ≔ exp" := (Write id addr) (at level 52).

Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
    | New _ _ v k => (* BindPT (NewPT v) (fun p => semantics (k p)) *)
        let pre := fun s => pre (semantics (k (alloc s))) s in 
        let post := fun s pres v' s' => 
                       post (semantics (k (alloc s))) s (pres) v' s' /\ 
                       (forall p, p <> alloc s -> find s p = find s' p) 
                       /\ find s' (alloc s) = Some (dyn _ v) in
        [pre , post]                                                    
    | Read _ _ ptr k => (* BindPT (ReadPT ptr) (fun v => semantics (k v)) *)
        let readPre := fun h => exists v, M.MapsTo ptr (dyn _ v) h in
        let pre := fun s => {p : readPre s & pre (semantics (k (read ptr s p))) s} in
        let post := fun s pres x s' => post (semantics (k (read ptr s (projT1 pres)))) s (projT2 pres) x s' in
        [pre , post]
    | Write _ _ ptr v k => 
        let writePre := fun s => M.In ptr s in
        let pre := fun s => writePre s /\ pre (semantics k) (update s ptr (dyn _ v)) in
        let post := fun s pres x s' => post (semantics k) (update s ptr (dyn _ v)) (proj2 pres) x s' in
        [pre , post]
    | While _ inv c body k => SeqPT (WhilePT inv c (semantics body)) (semantics k)
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
  | While _ Inv cond body c => While _ Inv cond (bind body k) (bind c k)
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

(*******************************************************************************
                   ****   Refinement of WhileL ****
*******************************************************************************)

Definition wrefines {a : Type} (w1 w2 : WhileL a) := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf.
Ltac destruct_units := destruct_all unit.
Ltac refine_unfold := unfold pre, post, subset, bind, "⟫="   in *.
Ltac refine_simpl := refine_unfold; intros; simpl in *; destruct_conjs; repeat split; repeat subst; destruct_units.
Ltac semantic_trivial := unfold semantics, pre, post; simpl; destruct_conjs; repeat split; now intuition.
Ltac exists_now :=
   match goal with
    | x : ?t |- { y : ?t & _} => exists x
    | x : ?t |- { y : ?t | _} => exists x
    | _ => idtac
   end.

Definition refineTrans {a} (w2 w1 w3 : WhileL a) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold_refinements; now apply refineTransPT.
  Defined.

Definition refineRefl {a} (w : WhileL a) :
  w ⊑ w.
    unfold_refinements; apply refineReflPT.
  Defined.

Definition refineSeq {a} (Pre Mid Post : Pow S) :
  let w := Spec a ([ Pre , fun _ _ _ => Post ]) in
  w ⊑ bind (Spec a ([Pre , fun _ _ _ => Mid ]))
           (fun _ => Spec a ([Mid , fun _ _ _ => Post ])).
Proof.
  apply refineBind.
Defined.

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
Lemma readStep {a b : Type} (w : WhileL a) (w' : b -> WhileL a)
  (ptr : Ptr)
  (H : pre (semantics w) ⊂ pre (semantics (Read a b ptr w')))
  (Q : forall s p x s', post (semantics (w' (read ptr s (projT1 (H s p))))) s (projT2 (H s p)) x s' -> post (semantics w) s p x s')
  : w ⊑ Read _ b ptr w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma readSpec {a b : Type} (spec : PT a) (w' : b -> WhileL a)
  (ptr : Ptr) (v : b)
  (H : pre (spec) ⊂ M.MapsTo ptr (dyn b v)) 
  (Step :  Spec _ ([ fun s => pre spec s, fun s pres x s' => post spec s (pres) x s' ]) ⊑ w' v) :
  Spec _ spec ⊑ Read _ b ptr w'.
Proof.
  eapply readStep.
  Unshelve.
  Focus 2.
  simpl.
  intros s H1.
  refine (existT _ _ _).
  Unshelve.
  Focus 2.
  exists v; now apply H.
  destruct (Step).
  simpl in *.
  rewrite (readMaps ptr v ).
  now apply d.
  now apply H.
  refine_simpl.
  destruct spec.
  destruct Step.
  simpl in *.
  apply s0.
  rewrite (readMaps ptr v) in H0.
  apply H0.
Qed.  

Lemma newStep {a b : Type} (w : WhileL a) (w' : Ptr -> WhileL a)
  (v : b)
  (H : pre (semantics w) ⊂ pre (semantics (New _ _ v w')))
  (Q : forall (s : S) (x : pre (semantics w) s) (v' : a),
   post (semantics (New _ _ v w')) s (H s x) v' ⊂ post (semantics w) s x v')
  : w ⊑ New _ _ v w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma newSpec {a b : Type} (spec : PT a) (w' : Ptr -> WhileL a) (v : b)
  (Step : forall p, Spec _ spec ⊑ w' p) :
  (* You would expect this hypothesis to say something about p pointing to v... *)
  Spec _ spec ⊑ New _ b v w'.
Proof.
  eapply newStep.
  Unshelve.
  Focus 2.
  refine_simpl.
  destruct spec.
  destruct (Step (alloc s)).
  simpl in *.
  apply d.
  apply H.
  simpl in *.
  refine_simpl.
  destruct spec.
  destruct Step.
  simpl in *.
  apply s1.
  apply H.
Qed.

Lemma assignStep {a b : Type} (w w' : WhileL a) (ptr : Ptr) (v : b)
  (h : pre (semantics w) ⊂ pre (semantics (Write _ _ ptr v w'))) 
  (h' : forall (s : S)(p : pre (semantics w) s)  (x : a) (s' : S), 
    post (semantics w') (update s ptr (dyn b v)) (proj2 (h s p)) x s' -> post (semantics w) s p x s')
  : w ⊑ Write _ _ ptr v w'.
  Proof.
    exact (Refinement _ _ h h').
  Qed.

Lemma refineAssign {a : Type} (w : WhileL unit) (ptr : Ptr) (x : a)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre tt (update s ptr (dyn a x)))
  (h' : pre (semantics w) ⊂ (fun h => M.In ptr h))
  : w ⊑ Write _ _ ptr x (Return _ tt).
  Proof.
    eapply assignStep. Unshelve. Focus 2.
    refine_simpl; now apply h'.
    refine_simpl; now apply h.
Qed.
  
Definition subst {a : Type} (ptr : Ptr) (v : a) (s : S) : S := 
   update s ptr (dyn a v).

Definition refineFollowAssignPre {a : Type} (ptr : Ptr) (x : a) (P : Pow S)
           (Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec unit ([P,fun s p _ s' => Q s p s']) in
  let w' := Spec unit ([P,fun s p _ s' => Q' s p s']) in
  forall (H : forall s pres s', Q' s pres s' -> (Q s pres (subst ptr x s')) /\ (M.In ptr s')),
  pre (semantics w) ⊂ pre (semantics (w' ; Write unit _ ptr x (Return unit tt))).
Proof.
  refine_simpl; exists_now.
  intros; split; [ eapply (H s _ _ _) | trivial].
  Unshelve. assumption. assumption.
Defined.

Lemma refineFollowAssign {a : Type} (ptr : Ptr) (x : a) (P : Pow S) 
(Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec _ ([P,fun s p _ s' => Q s p s']) in
  let w' := Spec unit ([P,fun s p _ s' => Q' s p s']) in
  (forall s pres s', Q' s pres s' -> (Q s pres (subst ptr x s')) /\ (M.In ptr s')) ->
  w ⊑ (w' ; Write _ _ ptr x (Return _ tt)).
Proof.
  intros w w' HQ.
  set (d := refineFollowAssignPre _ _ _ _ _ HQ :
             pre (semantics w) ⊂
             pre (semantics (w' ; Write unit _ ptr x (Return unit tt)))).
  apply (Refinement _ _ d); refine_simpl; now apply HQ.
Qed.

Definition refineFollowAssignPre' {a : Type} (ptr : Ptr) (P : Pow S) 
(Q : forall (s : S), P s -> Pow S) (Q' : forall (s : S), P s -> a -> Pow S) :
  let w  := Spec unit ([P,fun s pres _ s' => Q s pres s']) in
  let w' := Spec _ ([P,Q']) in
  (forall s pres v s', Q' s pres v s' -> prod (Q s pres (subst ptr v s')) (M.In ptr s')) ->
  (pre (semantics w) ⊂
      pre (semantics (bind w' (fun (v : a) => Write _ _ ptr v (Return _ tt))))).
Proof.
  intros w w' HQ; refine_simpl; exists_now.
  intros.
  intros; split; [ eapply (snd (HQ s _ _ _ _)) | trivial].
  Unshelve. assumption. assumption. assumption.
Defined.
  
Lemma refineFollowAssign' {a : Type} (ptr : Ptr) (P : Pow S) 
(Q : forall (s : S), P s -> Pow S) (Q' : forall (s : S), P s -> a -> Pow S) :
  let w  := Spec unit ([P,fun s pres _ s' => Q s pres s']) in
  let w' := Spec _ ([P,Q']) in
  (forall s pres v s', Q' s pres v s' -> prod (Q s pres (subst ptr v s')) (M.In ptr s')) ->
  w ⊑ (bind w' (fun v => Write _ _ ptr v (Return _ tt))).
Proof.
  intros w w' HQ; refine_simpl.
  apply (Refinement _ _ (refineFollowAssignPre' _ _ _ _ HQ)).
  refine_simpl; now eapply HQ. 
Qed.  

Ltac refine_assign ptr x := eapply (refineAssign _ ptr x _ _).
(* Wouter: this is a first approximation of this tactic, it probably needs to do quite a bit more... *)
  
Lemma refineSeqAssocR {a} : forall (w w1 w2 w3 : WhileL a),
  (w ⊑ (w1 ; w2) ; w3) -> (w ⊑ w1 ; w2 ; w3).
Proof.
  intros; apply (refineTrans ((w1; w2); w3)); [ assumption | ].
  set (d := (fun s pres => pres) : pre (semantics ((w1; w2); w3)) ⊂
                                  pre (semantics (w1; w2; w3))).
  apply (Refinement _ _ d); now trivial.
Defined.

Lemma refineSeqAssocL {a} : forall (w w1 w2 w3 : WhileL a),
  (w ⊑ w1 ; w2 ; w3) -> (w ⊑ (w1 ; w2) ; w3).
Proof.
  intros; apply (refineTrans (w1; w2; w3)); [ assumption | ].
  set (d := (fun s pres => pres) : pre (semantics (w1; w2; w3)) ⊂
                                  pre (semantics ((w1; w2); w3))).
  apply (Refinement _ _ d); now trivial.
Defined.

(** Just a brief example showing how the language currently looks like 
    Contains some testing definitions to be moved elsewhere once proven.
**)
Definition SWAP (p q : Ptr) : WhileL unit.
  refine (Spec _ _).
  refine (Predicate _ (fun s => M.In p s /\ M.In q s) _).
  intros s H t s'.
  refine (find s p = find s' q /\ find s q = find s' p).
Defined.

Hint Resolve Refinement.
Ltac while_refines a := unfold wrefines, preConditionOf, postConditionOf in *; refine_simpl; destruct_all (PT a).

Lemma refineReturn {a : Type} (w : WhileL a) (v : a)
  (H : forall (s : S) (pre : preConditionOf w s), postConditionOf w s pre v s) : 
  w ⊑ Return a v.
Proof.
  while_refines a; destruct (semantics w); eapply Refinement; refine_simpl; now eauto.
  Unshelve. refine_simpl.
Qed.

(* Definition undo *)

(* Lemma writeSpec {a b : Type} (spec : PT a) (w : WhileL a) *)
(*   (ptr : Ptr) (v : b) *)
(*   (H : forall s, pre spec s -> M.In ptr s) *)
(*   (Step :  Spec _  *)
(*     ([ fun s => exists s', update s' ptr (dyn _ v) = s /\ pre spec s', *)
(*        fun s pres x s' =>  *)
(*          exists t, update t ptr (dyn _ v) = s  *)
(*          /\ post spec t (pres) x s' ]) ⊑ w) : *)
(*   Spec _ spec ⊑ Write _ b ptr v w. *)
(* Proof. *)
(*   refine_simpl. *)
(*   destruct Step; destruct spec. *)
(*   eapply assignStep.   *)
(*   refine_simpl. *)
(*   Unshelve. *)
(*   apply s. *)
(*   refine_simpl. *)

(*   destruct (semantics w). *)
(*   apply H0. *)

(*   refine_simpl. *)
(*   now apply H. *)
(*   refine_simpl. *)
(*   unfold preConditionOf in *. *)
(*   destruct (semantics w). *)
(*   apply d. *)

  
(************************************************************

                             SWAP EXAMPLE

*************************************************************)

(* Lemma refineSplit {a : Type} *)
(*       (w1 w2 : WhileL a) *)
(*       (w3 : a -> WhileL a) : *)
(*       w1 ⊑ w2 -> *)
(*       bind w1 w3 ⊑ bind w2 w3. *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

(* Lemma refineSplit' {a : Type} *)
(*       (w1 w2 : WhileL a) *)
(*       (w3 w4 : a -> WhileL a) : *)
(*       w1 ⊑ bind w2 w3 -> *)
(*       bind w1 w4 ⊑ bind w2 (fun x => bind (w3 x) w4). *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

(* Lemma bindAssocR {a b c : Type} : *)
(*   forall (w1 : PT a) (w2 : a -> PT b) (w3 : b -> PT c), *)
(*     (w1 ⟫= w2) ⟫= w3 ⊏ w1 ⟫= (fun x => (w2 x) ⟫= w3). *)
(* Proof. *)
(* Admitted. *)

(* Lemma refineSplitPT {a b : Type} : *)
(*   forall (w1 w3 : PT a) (w2 w4 : a -> PT b), *)
(*   w1 ⊏ w3 -> *)
(*   (forall x, w2 x ⊏ w4 x) -> *)
(*   w1 ⟫= w2 ⊏ w3 ⟫= w4. *)
(* Proof. *)
(* Admitted. *)

(* Definition wouterSwap (P : Ptr) (Q : Ptr) (a : Type) : *)
(*   let SetQinN (s : Ptr -> WhileL unit) := *)
(*       (Read _ a Q) (fun v => New _ _ v s) in *)
(*   let SetPinQ (s : WhileL unit) := *)
(*       (Read _ a P) (fun v => Write _ _ Q v s) in *)
(*   let SetNinP (N : Ptr) (s : WhileL unit) := *)
(*       (Read _ a N) (fun v => Write _ _ P v s) in *)
(*   SWAP P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))). *)
(* Proof. *)
(*   intros. *)
(*   unfold SetQinN. *)
(*   eapply readSpec. *)
(*   refine_simpl. *)
(*   destruct H; auto. *)
(*   admit. *)
(*   (* Wouter: clearly need to use some lemmas about find... *) *)

(*
Lemma refineSplitReadNew {a : Type} (P : Ptr) (w1 : PT Ptr)
      (w2 : Ptr -> WhileL unit) :
      Spec _ w1 ⊑ Read Ptr a P (fun v : a => New Ptr a v (fun p => Return _ p)) ->
      bind (Spec _ w1) w2 ⊑ (Read unit a P (fun v : a => New unit a v w2)).
Proof.
  intros.
  unfold wrefines in *.
  simpl in *.
  apply (refineTransPT ((@ReadPT a P
     ⟫= NewPT) ⟫= (fun p : Addr.t => semantics (w2 p)))).
  apply refineSplitPT.
  destruct X.
  assert (d' : pre w1 ⊂ pre (@ReadPT a P ⟫= NewPT)).
  destruct w1.
  unfold subset in *; simpl in *.
  intros s' pre'.
  pose (d s' pre') as H.
  destruct H.
  exists x.
  intros.
  pose (s0 t v) as HH.
  now destruct HH.
  apply (Refinement _ _ d').
  intros.
  refine_simpl.
  destruct w1.
  apply s.
  repeat eexists; eauto.
  intros; apply refineReflPT.
  apply bindAssocR.
Defined.  
 *)

(* Lemma newSpec' {a b : Type} (spec : PT a) (w' : Ptr -> WhileL a) (v : b) *)
(*       (Step : forall p, Spec _ ([ fun s => prod (pre spec s) (M.In p s) , *)
(*                              fun s pres s' => post spec s (fst pres) s' ]) ⊑ w' p) : *)
(*   Spec _ spec ⊑ New _ b v w'. *)
(* Proof. *)
(*   apply newSpec. *)
(*   intros. *)
(*   pose (Step p). *)
(*   destruct spec; destruct w. *)
(*   refine_simpl. *)
(*   unfold wrefines; simpl in *. *)
(*   destruct (semantics (w' p)). *)
(*   assert (d' : Refinement.pre ([pre, p0]) ⊂ Refinement.pre ([pre0, p1])). *)
(*   simpl. unfold subset. intros. eapply d. *)
(*   split; auto. admit. *)
(*   eapply (Refinement _ _ d'). *)
(*   refine_simpl. *)
(* Admitted. *)
  

(* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
Definition swapResult (P : Ptr) (Q : Ptr) (a : Type) :
  let SetQinN (s : Ptr -> WhileL unit) :=
      (Read _ a Q) (fun v => New _ _ v s) in
  let SetPinQ (s : WhileL unit) :=
      (Read _ a P) (fun v => Write _ _ Q v s) in
  let SetNinP (N : Ptr) (s : WhileL unit) :=
      (Read _ a N) (fun v => Write _ _ P v s) in
  SWAP P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))).
Proof.
  intros.
  unfold SetQinN.
  eapply readSpec.
  refine_simpl.
  admit.
  eapply newSpec.
  intro N.
  unfold SetPinQ.
  eapply readSpec.
  refine_simpl.
  admit.
  eapply writeSpec.
  refine_simpl; auto.
  eapply readSpec.
  refine_simpl. admit.
  apply refineAssign; refine_simpl; auto.
  admit.
  admit.
  admit.  
Admitted.
  
(** End of example **)


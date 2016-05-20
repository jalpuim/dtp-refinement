Require Import Bool.
Require Import Heap.

Definition S := heap.

Definition Pow : Type -> Type := fun a => a -> Prop.

Definition K : forall {A} {a : Type}, Pow S -> (forall s:S, A s -> a -> Pow S) := fun a _ pt _ _ _ s => pt s.

Implicit Arguments K [A].

Definition subset : Pow S -> Pow S -> Prop :=
  fun P1 P2 => forall s, P1 s -> P2 s.

Notation "P1 ⊂ P2" := (subset P1 P2) (at level 80) : type_scope.

(* Extended PT to cover the return type  -- now the postcondition refers to the return value also *)
Inductive PT (a : Type) : Type :=
  Predicate : forall pre : Pow S, (forall s : S, pre s -> a -> Pow S) -> PT a.

Definition pre {a : Type} (pt : PT a) : Pow S := 
  match pt with
    | Predicate _ pre _ => pre
  end.

Definition post {a : Type} (pt : PT a) : (forall s : S, pre pt s -> a -> Pow S) :=
  match pt return (forall s : S, pre pt s -> a -> Pow S) with
    | Predicate _ _pre p => p
  end.

Inductive Refines {a : Type} (pt1 pt2 : PT a) : Type :=
  Refinement : 
    forall (d : pre pt1 ⊂ pre pt2), 
      (forall (s : S) (x : pre pt1 s) v, post pt2 s (d s x) v ⊂ post pt1 s x v) -> Refines pt1 pt2.

(* Joao: please double-check this definition *)
(* Wouter: It's OK I think. The question is where you quantify the v. 
I'd expect a predicate transformer on Pow (A*S) -> Pow (A*S)
Does that make sense?
*) 

Definition extend {a : Type} (pt : PT a) (v : a) (U : Pow S) : Pow S
  := fun s => { p : pre pt s & post pt s p v ⊂ U}.

Notation "PT1 ⊏ PT2" := (Refines PT1 PT2) (at level 90, no associativity) : type_scope.

Notation "[ p , q ]" := (Predicate _ p q) (at level 70) : type_scope.

Ltac refine_simpl := unfold subset, pre, post, extend; simpl; auto.

(*** Structural laws ***)

Lemma strengthenPost {a : Type} (P : Pow S) (Q1 Q2 : forall s, P s -> a -> Pow S) :
  (forall (s : S) (p : P s) (v : a), Q1 s p v ⊂ Q2 s p v) -> 
  [ P , Q2 ] ⊏ [ P , Q1 ].
Proof.
  intros.
  set (d := fun (s : S) (H: P s) => H).
  apply (Refinement ([P, Q2]) ([P, Q1]) d).
  intros. unfold post. unfold pre in x. unfold subset in *. intros. apply H.
  simpl in *; assumption.
Qed.

Lemma weakenPre {a : Type} (P1 P2 : Pow S) (f : P1 ⊂ P2) (Q : S -> a -> Pow S) :
  [P1, fun s _ => Q s ] ⊏ [P2 , fun s _ => Q s ].
Proof.
  intros.
  apply (Refinement ([P1, fun s _ => Q s]) ([P2, fun s _ => Q s]) f).
  unfold post,subset; intros; trivial.
Qed.

(*** SKIP **)

Definition Skip_PT {a : Type} : PT a := 
  let skipPre := fun s => True in
  let skipPost := fun s pres v s' => s = s' in
  [skipPre , skipPost].

(* Law 4.1 *)
Lemma refineSkip {a : Type} (pt : PT a) :
  (forall s (pres : pre pt s) v, post pt s pres v s) -> pt ⊏ Skip_PT.
  Proof.
    intros H; assert (d : pre pt ⊂ @pre a Skip_PT) by (unfold subset; simpl pre; auto).
    apply (Refinement pt Skip_PT d).
    simpl subset; intros s pres s' v eq; rewrite <- eq; auto.
  Qed.

(*
Lemma SkipExtendL {a : Type} (v : a) (U : Pow S) : extend v Skip_PT U ⊂ U.
  Proof.
    unfold extend; simpl subset; intros s [P1 P2]; apply P2; auto.
  Qed.

Lemma SkipExtendR {a : Type} (v : a) (U : Pow S) : U ⊂ extend v Skip_PT U.
  Proof.
    unfold extend, subset; intros s Us; simpl; split; [trivial | intros s' eq; rewrite <- eq; now trivial].
  Qed.
*)
(*** ASSIGNMENT ***)

Definition Assign_PT {a : Type} : (Pow S) -> (S -> S) -> PT a := fun p f =>
  let assignPre := p in
  let assignPost := fun s _ v s' => prod (s' = f s) (p s') in
  [assignPre , assignPost].

(* Law 1.3 *)
Lemma refineAssignPT {a : Type} (pt : PT a) (p : Pow S) (f : S -> S) (h : forall (s : S) (pre : pre pt s) (v : a),  post pt s pre v (f s)) (h' : pre pt ⊂ p)
  : pt ⊏ Assign_PT p f.
  Proof.
    assert (d : pre pt ⊂ @pre a (Assign_PT p f)); refine_simpl.
    eapply (Refinement pt (Assign_PT p f) d).
    simpl; intros s pres s' v' [eq p']; rewrite eq; auto.
  Qed.

(*** SEQUENCING (ignoring return values) **)
  
Definition Seq_PT {a : Type} (pt1 pt2 : PT a) : PT a :=
  let seqPre := fun s => {pres : pre pt1 s | forall t v, post pt1 s pres v t -> pre pt2 t} in
  let seqPost : forall s : S, seqPre s -> a -> Pow S := fun (s : S) (pres : seqPre s) (v : a) (s' : S) => 
    exists t : S, exists v, exists q : post pt1 s (proj1_sig pres) v t, post pt2 t (proj2_sig pres t v q) v s'
  in
  [seqPre , seqPost].

Notation "pt1 ;; pt2" := (Seq_PT pt1 pt2) (at level 52, right associativity).


Definition Bind_PT {a b : Type} (pt1 : PT a) (pt2 : a -> PT b) : PT b :=
  let seqPre := fun s => {pres : pre pt1 s | forall t v, post pt1 s pres v t -> pre (pt2 v) t} in
  let seqPost : forall s : S, seqPre s -> b -> Pow S := fun (s : S) (pres : seqPre s) (v : b) (s' : S) => 
    exists t : S, exists x, exists q : post pt1 s (proj1_sig pres) x t, post (pt2 x) t (proj2_sig pres t x q) v s'
  in
  [seqPre , seqPost].


(* Law 4.2 *)
Lemma refineSeqPT {a : Type} (Pre Mid Post : Pow S) :
  let pt := [ Pre , fun _ _ v s' => Post s' ] in
  pt ⊏ ([Pre , (fun _ _ v s' => Mid s') ] ;; [Mid , (fun _ _ (v : a) s' => Post s') ]).
  Proof.
    refine_simpl.
    assert (d : pre (Predicate _ Pre (K a Post)) ⊂ pre ([Pre , (K _ Mid) ] ;; [Mid , (K a Post) ])); refine_simpl.
    intros s pres; exists pres; auto.
    eapply (Refinement _ _ d).
    refine_simpl; intros s x v s' H; destruct H as [t [v' q]]; destruct q; auto.
Qed.


Require Import Bool.
Require Import Heap.
Require Import Program.Tactics.

Definition S := heap.

Definition Pow : Type -> Type := fun a => a -> Type.

Definition K : forall {A} {a : Type}, Pow S -> (forall s:S, A s -> a -> Pow S) := fun a _ pt _ _ _ s => pt s.

Definition Ka : forall {A} {a : Type}, (a -> Pow S) -> (forall s:S, A s -> a -> Pow S) := fun _ _ pt _ _ a s => pt a s.

Implicit Arguments K [A].

Implicit Arguments Ka [A].

Definition subset : Pow S -> Pow S -> Type :=
  fun P1 P2 => forall s, P1 s -> P2 s.

Notation "P1 ⊂ P2" := (subset P1 P2) (at level 80) : type_scope.

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

Notation "PT1 ⊏ PT2" := (Refines PT1 PT2) (at level 90, no associativity) : type_scope.

Notation "[ p , q ]" := (Predicate _ p q) (at level 70) : type_scope.

Ltac refine_simpl  := unfold subset, pre, post, K, Ka in *; intros; simpl in *.
Ltac destruct_pt a := refine_simpl; destruct_all (PT a).

(*** Structural laws ***)

Lemma strengthenPost {a : Type} (P : Pow S) (Q1 Q2 : forall s, P s -> a -> Pow S) :
  (forall (s : S) (p : P s) (v : a), Q1 s p v ⊂ Q2 s p v) -> 
  [ P , Q2 ] ⊏ [ P , Q1 ].
Proof.
  intros; set (d := fun (s : S) (H: P s) => H).
  apply (Refinement ([P, Q2]) ([P, Q1]) d).
  refine_simpl; now auto.
Qed.

Lemma weakenPre {a : Type} (P1 P2 : Pow S) (f : P1 ⊂ P2) (Q : S -> a -> Pow S) :
  [P1, fun s _ => Q s ] ⊏ [P2 , fun s _ => Q s ].
Proof.
  intros; apply (Refinement ([P1, fun s _ => Q s]) ([P2, fun s _ => Q s]) f).
  now refine_simpl.
Qed.

(*** SKIP **)

Definition SkipPT {a : Type} : PT a := 
  let skipPre := fun s => True in
  let skipPost := fun s pres v s' => s = s' in
  [skipPre , skipPost].

(* Law 4.1 *)
Lemma refineSkip {a : Type} (pt : PT a) :
  (forall s (pres : pre pt s) v, post pt s pres v s) -> pt ⊏ SkipPT.
  Proof.
    intros H; assert (d : pre pt ⊂ @pre a SkipPT) by (unfold subset; simpl pre; auto).
    apply (Refinement pt SkipPT d).
    destruct_pt a; subst; now trivial.
  Qed.

(*** ASSIGNMENT ***)

Definition AssignPT {a : Type} : (Pow S) -> (S -> S) -> PT a := fun p f =>
  let assignPre := p in
  let assignPost := fun s _ v s' => prod (s' = f s) (p s') in
  [assignPre , assignPost].

(* Law 1.3 *)
Lemma refineAssignPT {a : Type} (pt : PT a) (p : Pow S) (f : S -> S) (h : forall (s : S) (pre : pre pt s) (v : a),  post pt s pre v (f s)) (h' : pre pt ⊂ p)
  : pt ⊏ AssignPT p f.
  Proof.
    assert (d : pre pt ⊂ @pre a (AssignPT p f)) by (destruct_pt a; auto).
    eapply (Refinement pt (AssignPT p f) d).
    destruct_pt a; destruct_conjs; subst; now auto.
  Qed.

(*** SEQUENCING (ignoring return values) **)
  
Definition SeqPT {a : Type} (pt1 pt2 : PT a) : PT a :=
  let seqPre := fun s => {pres : pre pt1 s & forall t v, post pt1 s pres v t -> pre pt2 t} in
  let seqPost : forall s : S, seqPre s -> a -> Pow S := fun (s : S) (pres : seqPre s) (v : a) (s' : S) => 
  { t : S & {
    v : a & {
    q : post pt1 s (projT1 pres) v t &
    post pt2 t (projT2 pres t v q) v s'}}}
  in
  [seqPre , seqPost].

Notation "pt1 ;; pt2" := (SeqPT pt1 pt2) (at level 52, right associativity).

Definition BindPT {a b : Type} (pt1 : PT a) (pt2 : a -> PT b) : PT b :=
  let seqPre := fun s => {pres : pre pt1 s & forall t v, post pt1 s pres v t -> pre (pt2 v) t} in
               
  let seqPost : forall s : S, seqPre s -> b -> Pow S := fun (s : S) (pres : seqPre s) (v : b) (s' : S) =>
    {t : S & {
     x : a & {
     q : post pt1 s (projT1 pres) x t &
     post (pt2 x) t (projT2 pres t x q) v s'}}}
    (* exists t : S, exists x, exists q : post pt1 s (proj1_sig pres) x t, post (pt2 x) t (proj2_sig pres t x q) v s'*)
  in
  [seqPre , seqPost].

Notation "pt1 ⟫= pt2" := (BindPT pt1 pt2) (at level 52, right associativity).

Lemma refineSeqPT {a : Type} (Pre Mid Post : Pow S) :
  let pt := [ Pre , fun _ _ v s' => Post s' ] in
  pt ⊏ ([Pre , (fun _ _ v s' => Mid s') ] ;; [Mid , (fun _ _ (v : a) s' => Post s') ]).
  Proof.
    assert (d : pre (Predicate _ Pre (K a Post)) ⊂ pre ([Pre , (K _ Mid) ] ;; [Mid , (K a Post) ])).
    refine_simpl; split; now auto.
    eapply (Refinement _ _ d).
    refine_simpl; destruct_conjs; now auto.
Qed.

Lemma refineBindPT {a : Type} (Pre : Pow S) (Mid Post : a -> Pow S) :
  let pt := [ Pre , fun _ _ v s' => Post v s' ] in
  pt ⊏ BindPT ([Pre , (fun _ _ v s' => Mid v s') ]) (fun a => [ Mid a , (fun _ _ v s' => Post v s') ]).
  Proof.
    assert (d : pre (Predicate _ Pre (Ka _ Post)) ⊂ pre (BindPT ([Pre, Ka _ Mid])
       (fun v => [Mid v, Ka _ Post]))) by (refine_simpl; split; auto).
    eapply (Refinement _ _ d).
    refine_simpl; destruct_conjs; now auto.
Qed.
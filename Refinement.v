Require Import Bool.
Require Import Heap.
Require Import Program.Tactics.

(*******************************************************************************
                    ****   Basic definitions ****
*******************************************************************************)

Set Implicit Arguments.

Section Refinement.
  Variable t : Type.
  Definition S := heap t.

Definition Pred : Type -> Type := fun a => a -> Type.

Definition K : forall {A} {a : Type}, Pred S -> (forall s:S, A s -> a -> Pred S) := fun a _ pt _ _ _ s => pt s.

Definition Ka : forall {A} {a : Type}, (a -> Pred S) -> (forall s:S, A s -> a -> Pred S) := fun _ _ pt _ _ a s => pt a s.

Implicit Arguments K [A].

Implicit Arguments Ka [A].

Definition subset : Pred S -> Pred S -> Type :=
  fun P1 P2 => forall s, P1 s -> P2 s.

Notation "P1 ⊂ P2" := (subset P1 P2) (at level 80) : type_scope.

Record PT (a : Type) : Type :=
  MkPT { pre : Pred S;
         post : (forall s : S, pre s -> a -> Pred S) }.

(*
Definition pre {a : Type} (pt : PT a) : Pred S := 
  match pt with
    | MkPT pre _ => pre
  end.

Definition post {a : Type} (pt : PT a) : (forall s : S, pre pt s -> a -> Pred S) :=
  match pt return (forall s : S, pre pt s -> a -> Pred S) with
    | Predicate pre p => p
  end.
*)

Inductive Refines {a : Type} (pt1 pt2 : PT a) : Type :=
  Refinement : 
    forall (d : pre pt1 ⊂ pre pt2), 
      (forall (s : S) (x : pre pt1 s) v, post pt2 s (d s x) v ⊂ post pt1 s x v) -> Refines pt1 pt2.

Notation "PT1 ⊏ PT2" := (Refines PT1 PT2) (at level 90, no associativity) : type_scope.

Notation "[ p , q ]" := (MkPT p q) (at level 70) : type_scope.

Ltac refine_simpl  := unfold pre, post, K, Ka, subset in *; intros; simpl in *.
Ltac destruct_pt a := refine_simpl; destruct_all (PT a).

Definition semantics {A : Type} (pt : PT A) : Pred (A * S) -> Pred S
  := fun P s =>
      {p : pre pt s
       & forall s' v, post pt s p v s' -> P (v, s')}.

Lemma soundness1 {a : Type} (pt1 pt2 : PT a) :
  (pt1 ⊏ pt2) -> forall P, semantics pt1 P ⊂ semantics pt2 P.
  Proof.
    intros [H1 H2] P1 s [pre1 post1].
    exists (H1 s pre1).
    intros; apply post1; now apply H2.
  Qed.

Lemma soundness2 {a : Type} : forall (pt1 pt2 : PT a),
  (forall P, semantics pt1 P ⊂ semantics pt2 P) -> (pt1 ⊏ pt2).
Proof.
  intros [Pre1 Post1] [Pre2 Post2] H.
  set (Q := fun s pre => H (fun vs => Post1 s pre (fst vs) (snd vs)) s (existT _ pre (fun _ _ q => q))).
  eapply Refinement.
  Unshelve. Focus 2.
  unfold subset; simpl in *; now apply Q.
  intros s x v s' p; simpl in *; destruct (Q s x) as [p1 p2];
     now (apply p2).
  Qed.

Theorem soundness {A : Type} : forall (pt1 pt2 : PT A),
  (pt1 ⊏ pt2 -> (forall P, semantics pt1 P ⊂ semantics pt2 P))
  * ((forall P, semantics pt1 P ⊂ semantics pt2 P) -> pt1 ⊏ pt2).
  intros; split; [ now eapply soundness1 | eapply soundness2].
  Qed.

(*******************************************************************************
             ****   Primitive Predicate Transformers ****
*******************************************************************************)

Definition SkipPT {a : Type} : PT a := 
  let skipPre := fun s => True in
  let skipPost := fun s pres v s' => s = s' in
  [skipPre , skipPost].




(*******************************************************************************
                  ****   Basic refinement rules ****
*******************************************************************************)


Lemma strengthen {a : Type} (P : Pred S) (Q1 Q2 : forall s, P s -> a -> Pred S) :
  (forall (s : S) (p : P s) (v : a), Q1 s p v ⊂ Q2 s p v) -> 
  [ P , Q2 ] ⊏ [ P , Q1 ].
Proof.
  intros; set (d := fun (s : S) (H: P s) => H).
  apply (Refinement ([P, Q2]) ([P, Q1]) d).
  refine_simpl; now auto.
Qed.

Lemma weaken {a : Type} (P1 P2 : Pred S) (f : P1 ⊂ P2) (Q : S -> a -> Pred S) :
  [P1, fun s _ => Q s ] ⊏ [P2 , fun s _ => Q s ].
Proof.
  intros; apply (Refinement ([P1, fun s _ => Q s]) ([P2, fun s _ => Q s]) f).
  now refine_simpl.
Qed.

Lemma refineSkip {a : Type} (pt : PT a) :
  (forall s (pres : pre pt s) v, post pt s pres v s) -> pt ⊏ SkipPT.
  Proof.
    intros H; assert (d : pre pt ⊂ @pre a SkipPT) by (unfold subset; simpl pre; auto).
    apply (Refinement pt SkipPT d).
    destruct_pt a; subst; now trivial.
  Qed.

Definition refineTransPT {a} (pt2 pt1 pt3 : PT a) : 
  pt1 ⊏ pt2 -> pt2 ⊏ pt3 -> pt1 ⊏ pt3.
    intros [pre12 post12] [pre23 post23].
    set (d (s : S) (pre1s : pre pt1 s) := pre23 s (pre12 s pre1s)).
    refine (Refinement pt1 pt3 d _).
    now (destruct_pt a; auto).
  Defined.

Definition refineReflPT {a} (pt : PT a) : pt ⊏ pt.
  refine (Refinement pt pt (fun s pres => pres) _).
  now (destruct_pt a; auto).
  Defined.

Definition BindPT {a b : Type} (pt1 : PT a) (pt2 : a -> PT b) : PT b :=
  let seqPre := fun s => {pres : pre pt1 s & forall t v, post pt1 s pres v t -> pre (pt2 v) t} in
               
  let seqPost : forall s : S, seqPre s -> b -> Pred S := fun (s : S) (pres : seqPre s) (v : b) (s' : S) =>
    { t : S &
    { x : a &
    { q : post pt1 s (projT1 pres) x t &
     post (pt2 x) t (projT2 pres t x q) v s'}}}
  in
  [seqPre , seqPost].

Notation "pt1 ⟫= pt2" := (BindPT pt1 pt2) (at level 52, right associativity).

(* Definition NewPT (x : t) : PT Addr.t :=               *)
(*   Predicate _ (fun s => True)  *)
(*               (fun s _ p s' =>  *)
(*                  (forall p', p' <> p -> find _ s p = find _ s' p') *)
(*                  /\ find _ s' p = Some t). *)

(* Definition ReadPT {a : Type} (ptr : Addr.t) : PT a := *)
(*   Predicate _ (fun s => exists v, find s ptr = Some (dyn a v))  *)
(*               (fun s pres v s' => (s = s') /\ (Some (dyn a v) = find s ptr)). *)

Definition Is_false (b : bool) :=
  match b with
    | true => False
    | false => True
  end.

Definition WhilePT {a : Type} (inv : S -> Type) (cond : S -> bool) (body : PT a) : PT a :=
  let whilePre := (fun s =>   (* The invariant should hold initially *)
                             prod (inv s)
                              (* If we enter the loop, the precondition of the body should hold *)
                            { H : (forall s, prod (Is_true (cond s)) (inv s) -> pre body s) &
                              (* The loop body should preserve the invariant *)
                            (forall s v s' (t : prod (Is_true (cond s)) (inv s)), post body s (H s t) v s' -> inv s')})                          
  in
  let whilePost := (fun _ _ _ s' => prod (inv s') (Is_false (cond s'))) in
  [ whilePre , whilePost ].

Definition WhilePT' {a : Type} (* inv: initial state -> current state -> Type*)
           (inv : S -> S -> Type) (cond : S -> bool) (body : PT a) : PT a :=
  let whilePre := (fun si =>   (* The invariant should hold initially *)
                             prod (inv si si)
                              (* If we enter the loop, the precondition of the body should hold *)
                            { H : (forall s, prod (Is_true (cond s)) (inv si s) -> pre body s) &
                              (* The loop body should preserve the invariant *)
                            (forall s v s' (t : prod (Is_true (cond s)) (inv si s)), post body s (H s t) v s' -> inv si s')})                          
  in
  let whilePost := (fun s _ _ s' => prod (inv s s') (Is_false (cond s'))) in
  [ whilePre , whilePost ].

Definition SeqPT {a b : Type} (pt1 : PT a) (pt2 : PT b) : PT b :=
  let seqPre := fun s => { pres : pre pt1 s & forall t v, post pt1 s pres v t -> pre pt2 t} in
  let seqPost : forall s : S, seqPre s -> b -> Pred S := fun (s : S) (pres : seqPre s) (v : b) (s' : S) => 
  {t : S &
  {v' : a &
  {q : post pt1 s (projT1 pres) v' t &
   post pt2 t (projT2 pres t v' q) v s'}}} in
  [seqPre , seqPost].


Notation "pt1 ;; pt2" := (SeqPT pt1 pt2) (at level 52, right associativity).


End Refinement.
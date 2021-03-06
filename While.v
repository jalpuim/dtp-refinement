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
  | While  : (S v -> S v -> Type) -> (S v -> bool) -> WhileL unit -> WhileL a -> WhileL a
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
      
      MkPT pre post
    | Read ptr k =>
      let readPre := fun h => { x : v & find h ptr = Some x} in
      let pre := fun s => {p : readPre s & pre (semantics (k (projT1 p))) s} in
      let post := fun s pres x s' => 
                    post (semantics (k (projT1 (projT1 pres)))) s (projT2 pres) x s' in
      MkPT pre post
    | Write ptr x k => 
      let pre := fun s => 
                   prod ({y : v & find s ptr = Some y})
                        (pre (semantics k) (update s ptr x)) in
      let post := fun s pres res s' =>
                    post (semantics k) (update s ptr x) (snd pres) res s' in
      MkPT pre post
    | While inv c body k => SeqPT (WhilePT' inv c (semantics body)) (@semantics a k)
    | Spec s => s
    | Return  x => MkPT (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition preConditionOf {a : Type} (w : WhileL a) : Pred (S v) :=
  match semantics w with
    | MkPT p _ => p
  end.

Definition postConditionOf {a : Type} (w : WhileL a)
  : (forall s : (S v), preConditionOf w s -> a -> Pred (S v)) :=
  match semantics w as x return (forall s : (S v), match x with | MkPT p _ => p end s -> a -> Pred (S v)) with
    | MkPT pre post => post
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
                   ****   Refinement constructs ****
*******************************************************************************)

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
  (Step : forall v, Spec (MkPT (fun s => prod (pre spec s)
                                                    (find s ptr = Some v))
                                      (fun s pres x s' => post spec s (fst pres) x s')) ⊑ w' v) :
  Spec spec ⊑ Read ptr w'.
Proof.
  unshelve eapply readRefines.
  * refine_simpl; assert (valid : {y : v & find s ptr = Some y}) by now apply H.
    exists valid. 
    destruct valid as [x P]; destruct (Step x) as [d h].
    refine_simpl; destruct (semantics (w' x)); destruct spec.
    apply d; split; auto.

  * intros; destruct spec; refine_simpl.
    generalize X; generalize (H s p).
    intros [A1 A2] B; destruct (Step A1) as [d h].
    refine_simpl.
    destruct (semantics (w' A1)).
    set (Ha := pair p A2 : (pre s * (find s ptr = Some (A1)))).
    pose (h s Ha x s').
    now eauto.
Qed.

Lemma readStep {a : Type} (ptr : Ptr)  (spec : PT _ a) 
  (H : forall s, pre (spec) s -> {y : v & find s ptr = Some y})
  (Step : {w : v -> WhileL a &
            forall y, 
            Spec (MkPT (fun s => prod (pre spec s)
                                   (find s ptr = Some y))
                    (fun s pres x s' => post spec s (fst pres) x s' )) ⊑ w y}) :
  {w : WhileL a & Spec spec ⊑ w}.
Proof.
  destruct Step as [w A]; exists (Read ptr w); now apply readSpec.
Qed.

Lemma newRefines {a : Type} (w : WhileL a) (w' : Ptr -> WhileL a)
  (y : v)
  (H : subset (pre (semantics w)) (pre (semantics (New y w'))))
  (Q : forall (s : S v) (x : pre (semantics w) s) (v' : a),
   subset (post (semantics (New y w')) s (H s x) v') (post (semantics w) s x v'))
  : w ⊑ New y w'.
Proof.
  exact (Refinement _ _ H Q).
Qed.  

Lemma newSpec {a : Type} (y : v) (spec : PT v a) (w : Ptr -> WhileL a)
      (Step : forall p, Spec (MkPT (fun s => { t : S v & prod (pre spec t)
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
    repeat split; eauto.
    unfold not; intros p' HIn HEq; subst.
    apply (allocDiff1 _ HEq).
  * refine_simpl; destruct spec; destruct (Step (alloc s)).
    destruct (semantics (w (alloc s))).
    now apply s1 in X.
Qed.

Lemma newStep {a : Type} (y : v) (spec : PT _ a)
      (Step : {w : (Ptr -> WhileL a) & forall (p : Ptr),
                Spec (MkPT (fun s => { t : S v & prod (pre spec t)
                                            (prod (forall p' x, find t p' = Some x -> p' <> p)
                                                  (s = (update t p (y)))) })
                        (fun s pres v s' => post spec (projT1 pres) (fst (projT2 pres)) v s')) ⊑ w p}) :
  {w : WhileL a & Spec spec ⊑ w}.
  Proof.
    destruct Step as [w S]; exists (New y w); now apply newSpec.
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
    (MkPT  (fun s => {t : S v & prod (pre spec t) (s = (update t ptr (y)))})
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
    (MkPT (fun s => {t : S v & prod (pre spec t) (s = (update t ptr y))})
       (fun s pres x s' => 
              (post spec (projT1 pres) (fst (projT2 pres)) x s'))) ⊑ w}) :
  {w : WhileL a & Spec spec ⊑ w}.
  Proof.
    destruct Step as [w' A]; exists (Write ptr y w'); now apply writeSpec.
  Qed.

Lemma returnStep {a : Type} (x : a) (w : WhileL a) 
  (H : forall (s : S v) (pre : preConditionOf w s), postConditionOf w s pre x s) : 
  w ⊑ Return x.
Proof.
  unshelve eapply Refinement; refine_simpl; apply H.
Qed.

(** While (loop) **)

Lemma whileRefines {a : Type} (I : S v -> S v -> Type) (c : S v -> bool) (body : WhileL unit) (w k : WhileL a)
  (d : subset (pre (semantics w)) (pre (semantics (While I c body k))))
  (h : forall (s : S v)(p : pre (semantics w) s) (x : a) (s' : S v), 
    post (semantics (While I c body k)) s (d s p) x s' -> post (semantics w) s p x s')
  : w ⊑ While I c body k.
  Proof.
    exact (Refinement _ _ d h).
  Qed.


Lemma whileSpec {a : Type} (I : S v -> S v -> Type) (c : S v -> bool) (spec : PT _ a) (k : WhileL a) (body : WhileL unit)
  (d : forall s, pre spec s -> I s s)
  (refineBody : Spec (MkPT (fun s => {t : S v & prod (I t s) (Is_true (c s))}) (fun s pres _ s' => I (projT1 pres) s')) ⊑ body)
  (refineRest : Spec (MkPT (fun s => {t : S v & prod (pre spec t) (
                                                     prod (I t s) (
                                                          (Is_false (c s))
                                          (* This states that there is some initial state t that satisfies the precondition of spec
                                             such that we can go from t to a new state s (after having run through the loop) 
                                             Question: should s and t be related somehow?
                                           *)
                                          ))})
                                (fun s pres x s' => post spec (projT1 pres) (fst (projT2 pres)) x s')
                     ) 
                ⊑ k )
  :
  Spec spec ⊑ While I c body k.
  Proof.
    unshelve econstructor; destruct spec as [pre post]; destruct refineRest as [d1 h1]; destruct refineBody as [d2 h2]; refine_simpl.
    * now eauto.
    * unshelve econstructor; refine_simpl. apply d2. exists s; split; auto.
      destruct (semantics body).
      destruct (semantics k).
      pose (h2 s).
      assert (Ha := h2 _ _ _ _ X0).
      now simpl in Ha.
    * refine_simpl; eapply d1; unshelve econstructor; [exact s | now eauto].
    * refine_simpl. unshelve refine (h1 X (existT _ s ( x , _)) _ _ _); [now eauto | eassumption ].
  Qed.

Lemma changeSpec {a : Type} (pt1 pt2 : PT _ a) (w : WhileL a)
  (d : subset (pre pt2) (pre pt1))
  (h : forall (s : S v) (x : pre pt2 s) y, subset (post pt1 s (d s x) y) (post pt2 s x y))
  (H : Spec pt1 ⊑ w) :
  Spec pt2 ⊑ w.
  Proof.
    eapply refineTrans; [ | apply H]; exact (Refinement _ _ d h).
  Qed.
  
Lemma ifSpec {a} (cond : bool) (spec : PT _ a) (wt we : WhileL a) :
  (if cond then Spec spec ⊑ wt else Spec spec ⊑ we) ->
  (Spec spec ⊑ (if cond then wt else we)).
Proof. destruct cond; intros; assumption. Qed.

  
End WHILE.

(************************************************************

                             TACTICS

*************************************************************)


Hint Resolve allocDiff1 allocDiff2 heapGrows someExists someExistsT someIn findAlloc1 findAlloc2 freshDiff1 freshDiff2 not_eq_sym.
Hint Resolve findUpdate findNUpdate1 findNUpdate2.
Hint Resolve allocFresh findAlloc1 findAlloc2.

Hint Rewrite findUpdate findNUpdate : Heap.

(* Simple tactics *)
Ltac destruct_conjs' := repeat ((destruct_one_pair || destruct_one_ex); simpl).
Ltac refine_unfold := unfold pre, post, subset, bind in *.
Ltac refine_simpl := 
  refine_unfold; intros; simpl in *; destruct_conjs'; 
  repeat split; repeat subst; simpl in *.
Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf in *.

Ltac simpl_goal :=  refine_simpl; eauto.
Ltac context_simpl :=
  repeat match goal with
           | [H1 : find ?s ?T = Some ?x, H2 : find ?s ?T = Some ?y |- _ ] => assert (E : x = y) by (eapply (findUnique _ _ H1 H2)); subst x; clear H2
           | [H1 : find ?s ?T = Some ?x, H2 : find ?s ?T = Some ?y |- _ ] => rewrite H2 in H1; inversion H1; subst
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
Ltac READ ptr v := eapply (readSpec ptr); [ | intros v]; simpl_goal.
Ltac NEW v ptr := eapply (@newSpec _ _ v); intros ptr; simpl_goal.
Ltac WRITE ptr v := eapply (@writeSpec _ _ ptr v); simpl_goal.
Ltac ASSERT P := unshelve eapply (changeSpec P); simpl_goal.
Ltac RETURN v := eapply (returnStep v); unfold_refinements; refine_simpl; context_simpl; context_clean.
Ltac WHILE I c := apply (whileSpec I c); simpl_goal.
Ltac IFF c := apply (ifSpec c); remember c as b; destruct b; simpl_goal.

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity).




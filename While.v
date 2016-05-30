Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Heap.
Require Import Refinement.
Require Import Program.Tactics.
Module Language.

(*******************************************************************************
                    ****   The While language ****
*******************************************************************************)

Definition Ptr := Addr.t.

Inductive WhileL (a : Type) : Type :=
  | New    : forall v, v -> (Ptr -> WhileL a) -> WhileL a
  | Read   : forall v, Ptr -> (v -> WhileL a) -> WhileL a
  | Write : forall {v}, Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S -> Prop) -> (S -> bool) -> WhileL a -> WhileL a
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "addr ≔ exp" := (Write id addr) (at level 52).

Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
    | New _ _ v k => BindPT (NewPT v) (fun p => semantics (k p))
    | Read _ _ ptr k => BindPT (ReadPT ptr) (fun v => semantics (k v))
    | Write _ ptr v k => 
      SeqPT (AssignPT (fun h => M.In ptr h) (fun s => (update s ptr (dyn _ v))))
             (semantics k)            
    | While _ inv c body => WhilePT inv c (semantics body)
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
  | Write _ p v c => Write _ p v (bind c k)
  | While _ Inv cond body => While _ Inv cond (bind body k)
  | Spec _ pt => Spec _ (BindPT pt (fun x => semantics (k x)))
  | Return _ x => k x
  end.

Notation "a ; b" := (bind a (fun _ => b)) (at level 60).

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ _ _ k     => forall ptr, isExecutable (k ptr)
    | Read _ _ _ k    => forall v, isExecutable (k v)
    | Write _ _ _ w   => isExecutable w
    | While _ inv c b => isExecutable b
    | Spec _ pt       => False
    | Return _ a      => True
  end.

(*******************************************************************************
                   ****   Refinement of WhileL ****
*******************************************************************************)

Definition wrefines {a : Type} (w1 w2 : WhileL a) := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf.

Definition refineTrans {a} (w2 w1 w3 : WhileL a) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold_refinements; now apply refineTransPT.
  Defined.

Definition refineRefl {a} (w : WhileL a) :
  w ⊑ w.
    unfold_refinements; apply refineReflPT.
  Defined.

Definition refineBind {a} (Pre : Pow S) (Mid Post : a -> Pow S) :
  let w := Spec _ ([ Pre , fun _ _ => Post ]) in
  w ⊑ bind (Spec _ ([Pre , fun _ _ => Mid ]))
           (fun a => Spec _ ([Mid a , fun _ _ => Post ])).

  unfold_refinements; simpl.
  assert (d : pre ([Pre, fun (s : S) (_ : Pre s) => Post]) ⊂
       pre ([fun s : S =>
      {_ : Pre s & forall (s' : S) (v : a), Mid v s' -> Mid v s'},
     fun (s : S)
       (_ : {_ : Pre s & forall (s' : S) (v : a), Mid v s' -> Mid v s'})
       (y : a) (s'' : S) =>
       { s' : S & { x : a & {_ : Mid x s' & Post y s''} } }])).
  unfold subset; simpl in *; destruct_conjs; intros; split; auto.
  apply (Refinement _ _ d).  
  unfold post, subset; intros; destruct_conjs; now trivial.
Defined.

Definition refineSeq {a} (Pre Mid Post : Pow S) :
  let w := Spec a ([ Pre , fun _ _ _ => Post ]) in
  w ⊑ bind (Spec a ([Pre , fun _ _ _ => Mid ]))
           (fun _ => Spec a ([Mid , fun _ _ _ => Post ])).
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
  apply (Refinement _ _ d);
  intros; destruct_pt a; auto.
Defined.

Lemma refineWhilePT {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) : 
  let pt := [inv , fun _ _ _ s' => inv s' /\ Q s'] in
  let body : PT a := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  (forall s, Is_false (cond s) -> Q s) ->
  pt ⊏ WhilePT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (WhilePT inv cond body)).
    refine_simpl; repeat split; destruct_conjs; auto.
    apply (Refinement _ _ d).
    intros; repeat split; refine_simpl; destruct_conjs; now auto.
Qed.

Lemma refineWhile {a} (inv : S -> Prop) (cond : S -> bool) (Q : S -> Prop) 
  (StrQ : forall s, Is_false (cond s) -> Q s) : 
  let w := Spec a ([inv , fun _ _ _ s' => inv s' /\ Q s']) in
  let body := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  w ⊑ While a inv cond (Spec a body).
  Proof.
    refine_simpl; now (apply refineWhilePT).
  Qed.

Ltac destruct_units := destruct_all unit.
Ltac refine_simpl := unfold pre, post, subset; intros; simpl in *; destruct_conjs; repeat split; repeat subst; destruct_units.
Ltac semantic_trivial := unfold semantics, pre, post; simpl; destruct_conjs; repeat split; now intuition.

Lemma refineAssign {a : Type} (w : WhileL unit) (ptr : Ptr) (x : a)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre tt (update s ptr (dyn a x)))
  (h' : pre (semantics w) ⊂ (fun h => M.In ptr h))
  : w ⊑ Write _ ptr x (Return _ tt).
  Proof.
    assert (d: pre (semantics w) ⊂ pre (semantics (Write _ ptr x (Return _ tt)))) by
      (destruct (semantics w); semantic_trivial).
    apply (Refinement _ _ d); refine_simpl; destruct (semantics w); now eapply h.
  Qed.
  
Definition subst {a : Type} (ptr : Ptr) (v : a) (s : S) : S :=  update s ptr (dyn a v).

Definition refineFollowAssignPre {a : Type} (ptr : Ptr) (x : a) (P : Pow S)
           (Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec unit ([P,fun s p _ s' => Q s p s']) in
  let w' := Spec unit ([P,fun s p _ s' => Q' s p s']) in
  (forall s pres s', Q' s pres s' -> prod (Q s pres (subst ptr x s')) (M.In ptr s')) ->
  pre (semantics w) ⊂ pre (semantics (w' ; Write unit ptr x (Return unit tt))).
  intros w w' HQ.
  refine_simpl.
  unfold preConditionOf; simpl.
  exists X.
  intros s' v H'.
  apply HQ in H' as [H' HIn].
  exists HIn.
  intros s'' v' H''.
  apply I.
Defined.

Lemma refineFollowAssign {a : Type} (ptr : Ptr) (x : a) (P : Pow S) 
(Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec _ ([P,fun s p _ s' => Q s p s']) in
  let w' := Spec unit ([P,fun s p _ s' => Q' s p s']) in
  (forall s pres s', Q' s pres s' -> prod (Q s pres (subst ptr x s')) (M.In ptr s')) ->
  w ⊑ (w' ; Write _ ptr x (Return _ tt)).
Proof.
  intros w w' HQ.
  set (d := refineFollowAssignPre _ _ _ _ _ HQ :
             pre (semantics w) ⊂
             pre (semantics (w' ; Write unit ptr x (Return unit tt)))).
  apply (Refinement _ _ d); refine_simpl.
  unfold subset, preConditionOf, postConditionOf in *.
  simpl in *.
  now apply HQ.
Qed.

Definition refineFollowAssignPre' {a : Type} (ptr : Ptr) (P : Pow S) 
(Q : forall (s : S), P s -> Pow S) (Q' : forall (s : S), P s -> a -> Pow S) :
  let w  := Spec unit ([P,fun s pres _ s' => Q s pres s']) in
  let w' := Spec _ ([P,Q']) in
  (forall s pres v s', Q' s pres v s' -> prod (Q s pres (subst ptr v s')) (M.In ptr s')) ->
  (pre (semantics w) ⊂
      pre (semantics (bind w' (fun (v : a) => Write _ ptr v (Return _ tt))))).
Proof.
  intros w w' HQ.
  refine_simpl.
  unfold preConditionOf; simpl.
  exists X.
  intros s' v H'.
  apply HQ in H' as [H' HIn].
  exists HIn.
  intros s'' v' H''.
  apply I.
Defined.
  
Lemma refineFollowAssign' {a : Type} (ptr : Ptr) (P : Pow S) 
(Q : forall (s : S), P s -> Pow S) (Q' : forall (s : S), P s -> a -> Pow S) :
  let w  := Spec unit ([P,fun s pres _ s' => Q s pres s']) in
  let w' := Spec _ ([P,Q']) in
  (forall s pres v s', Q' s pres v s' -> prod (Q s pres (subst ptr v s')) (M.In ptr s')) ->
  w ⊑ (bind w' (fun v => Write _ ptr v (Return _ tt))).
Proof.
  intros w w' HQ.
  unfold "⊑".
  apply (Refinement _ _ (refineFollowAssignPre' _ _ _ _ HQ)); refine_simpl.
  unfold subset, preConditionOf, postConditionOf in *.
  simpl in *.
  repeat destruct H2; subst.
  eapply fst.
  now eapply HQ. 
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

Lemma refineRead {a : Type} (w : WhileL unit) (w' : a -> WhileL unit)
  (ptr : Ptr)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre tt s)
  (h' : pre (semantics w) ⊂ (fun s => M.In ptr s))
  : w ⊑ Read _ a ptr w'.
Proof.
  assert (d: pre (semantics w) ⊂ pre (semantics (Read unit a ptr w'))).
  destruct (semantics w); refine_simpl.
  unfold subset in *.
  apply h' in X.
  eexists. 
  intros t v H.
  destruct (semantics (w' v)).
  simpl.
  
Admitted.

(** Just a brief example showing how the language currently looks like **)
Definition SWAP : WhileL unit.
  apply (Spec _).
  refine (Predicate _ (fun s => (prod {p : Ptr | M.In p s}
                                     {q : Ptr | M.In q s})) _).
  intros s [[P PinS] [Q QinS]] tt.
  refine (fun s' => find s P = find s' Q /\ find s Q = find s' P).
Defined.

(* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
(* This definition is incorrect. *)
Definition swapResult (a : Type) :
  let SetQinN (Q : Ptr) (s : Ptr -> WhileL unit) :=
      (Read _ a Q) (fun v => New _ _ v s) in
  let SetPinQ (P : Ptr) (Q : Ptr) (s : WhileL unit) :=
      (Read _ a P) (fun v => Write _ Q v s) in
  let SetNinP (P : Ptr) (N : Ptr) (s : WhileL unit) :=
      (Read _ a N) (fun v => Write _ P v s) in
  { P : Ptr & ( { Q : Ptr &
  SWAP ⊑ SetQinN Q (fun N => SetPinQ P Q (SetNinP P N (Return _ tt))) })}.
Proof.
  unfold SWAP; simpl.
  
  (*
  eapply refineFollowAssign' with (ptr := P).
                                 (Q' := fun s _ _ s' => find s Q = find s' N
                                                   /\ find s P = find s' Q
                                                   /\ M.In P s' /\ M.In Q s' /\ M.In N s').
  *)
Admitted.

(* Alternative spec *)
Definition SWAP' (P : Ptr) (Q : Ptr) : WhileL unit.

  apply (Spec _).
  refine (Predicate _ (fun s => prod (M.In P s) (M.In Q s)) _).
  intros.
  refine (fun s' => find s P = find s' Q /\ find s Q = find s' P).
Defined.

Definition swapResult' (P : Ptr) (Q : Ptr) (a : Type) :
  let SetQinN (s : Ptr -> WhileL unit) :=
      (Read _ a Q) (fun v => New _ _ v s) in
  let SetPinQ (s : WhileL unit) :=
      (Read _ a P) (fun v => Write _ Q v s) in
  let SetNinP (N : Ptr) (s : WhileL unit) :=
      (Read _ a N) (fun v => Write _ P v s) in
  SWAP' P Q ⊑ SetQinN (fun N => SetPinQ (SetNinP N (Return _ tt))).
Proof.
Admitted.
  
(** End of example **)

(* Joao: I stopped here *)

End Semantics.


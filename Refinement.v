(* TODO: 
  - How to deal with allocation of vars? 
    Maybe its better to handle this from the outset
  - Total vs partial correctness. Should we worry about the 
    variant of a while?
  - How to handle frame rules? What can change and what cannot?
*)

Require Import Bool.

Record S : Type := mkS {varN : nat; varP : nat; varQ : nat; varR : nat}.

Definition Pow : Type -> Type := fun a => a -> Prop.

Definition K : forall {A}, Pow S -> (forall s:S, A s -> Pow S) := fun a pt _ _ s => pt s.

Implicit Arguments K [A].

Definition subset : Pow S -> Pow S -> Prop :=
  fun P1 P2 => forall s, P1 s -> P2 s.

Notation "P1 ⊂ P2" := (subset P1 P2) (at level 80) : type_scope.

Inductive PT : Type :=
  Predicate : forall pre : Pow S, (forall s : S, pre s -> Pow S) -> PT.

Definition pre (pt : PT) : Pow S := 
  match pt with
    | Predicate pre _ => pre
  end.

Definition post (pt : PT) : (forall s : S, pre pt s -> Pow S) :=
  match pt return (forall s : S, pre pt s -> Pow S) with
    | Predicate _pre p => p
  end.

Definition extend (pt : PT) (U : Pow S) : Pow S := 
  fun s => { p : pre pt s & post pt s p ⊂ U}.

Inductive Refines (pt1 pt2 : PT) : Type :=
  Refinement : 
    forall (d : pre pt1 ⊂ pre pt2), 
      (forall (s : S) (x : pre pt1 s), post pt2 s (d s x) ⊂ post pt1 s x) -> Refines pt1 pt2.

Notation "PT1 ⊏ PT2" := (Refines PT1 PT2) (at level 90, no associativity) : type_scope.

Notation "[ p , q ]" := (Predicate p q) (at level 70) : type_scope.

Ltac refine_simpl := unfold subset, pre, post, extend; simpl; auto.

(*** Structural laws ***)

Lemma strengthenPost (P : Pow S) (Q1 Q2 : forall s, P s -> Pow S) :
  (forall (s : S) (p : P s), Q1 s p ⊂ Q2 s p) -> 
  [ P , Q2 ] ⊏ [ P , Q1 ].
Proof.
  intros.
  set (d := fun (s : S) (H: P s) => H).
  apply (Refinement ([P, Q2]) ([P, Q1]) d).
  intros. unfold post. unfold pre in x. unfold subset in *. intros. apply H.
  simpl in *; assumption.
Qed.

Lemma weakenPre (P1 P2 : Pow S) (Q : forall s, P2 s -> Pow S) (f : P1 ⊂ P2) :
  [ P1 , (fun s p s' => Q s (f s p) s') ] ⊏ [ P2 , Q ].
Proof.
  intros.
  apply (Refinement ([P1, fun (s : S) (p : P1 s) (s' : S) => Q s (f s p) s']) ([P2, Q]) f).
  intros. unfold post. unfold subset. intros. trivial.
Qed.


(*** SKIP **)

Definition Skip_PT : PT := 
  let skipPre := fun s => True in
  let skipPost := fun s pres s' => s = s' in
  [skipPre , skipPost].

(* Law 4.1 *)
Lemma refineSkip (pt : PT) : (forall s (pres : pre pt s), post pt s pres s) -> pt ⊏ Skip_PT.
  Proof.
    intros H; assert (d : pre pt ⊂ pre Skip_PT) by (unfold subset; simpl pre; auto).
    apply (Refinement pt Skip_PT d).
    simpl subset; intros s pres s' eq; rewrite <- eq; auto.
  Qed.

Lemma SkipExtendL (U : Pow S) : extend Skip_PT U ⊂ U.
  Proof.
    unfold extend; simpl subset; intros s [P1 P2]; apply P2; auto.
  Qed.

Lemma SkipExtendR (U : Pow S) : U ⊂ extend Skip_PT U.
  Proof.
    unfold extend, subset; intros s Us; simpl; split; [trivial | intros s' eq; rewrite <- eq; now trivial].
  Qed.


(*** ASSIGNMENT ***)

Definition Assign_PT : (S -> S) -> PT := fun f =>
  let assignPre := fun s => True in
  let assignPost := fun s _ s' => s' = f s in
  [assignPre , assignPost].

(* Law 1.3 *)
Lemma refineAssignPT (pt : PT) (f : S -> S) (h : forall (s : S) (pre : pre pt s),  post pt s pre (f s)) 
  : pt ⊏ Assign_PT f.
  Proof.
    assert (d : pre pt ⊂ pre (Assign_PT f)); refine_simpl.
    eapply (Refinement pt (Assign_PT f) d).
    simpl; intros s pres s' eq; rewrite eq; auto.
  Qed.

Lemma AssignExtendL (U : Pow S) (f : S -> S) (s : S) : extend (Assign_PT f) U s -> U (f s).
  Proof.
    unfold extend; intros [H1 H2]; apply H2; reflexivity.
  Qed.

Lemma AssignExtendR  (U : Pow S) (f : S -> S) (s : S) : U (f s) -> extend (Assign_PT f) U s.
  Proof.
    intros Ufs; unfold extend; simpl; split; [ trivial | unfold subset; intros s' eq; rewrite eq; now trivial].
  Qed.


(*** SEQUENCING **)

Definition Seq_PT (pt1 pt2 : PT) : PT :=
  let seqPre := fun s => {pres : pre pt1 s | forall t, post pt1 s pres t -> pre pt2 t} in
  let seqPost : forall s : S, seqPre s -> Pow S := fun (s : S) (pres : seqPre s) (s' : S) => 
    exists t : S, exists q : post pt1 s (proj1_sig pres) t, post pt2 t (proj2_sig pres t q) s'
  in
  [seqPre , seqPost].

Notation "pt1 ;; pt2" := (Seq_PT pt1 pt2) (at level 52, right associativity).

(* Law 4.2 *)
Lemma refineSeqPT (Pre Mid Post : Pow S) :
  let pt := [ Pre , fun _ _ s' => Post s' ] in
  pt ⊏ ([Pre , (fun _ _ s' => Mid s') ] ;; [Mid , (fun _ _ s' => Post s') ]).
  Proof.
    refine_simpl.
    assert (d : pre (Predicate Pre (K Post)) ⊂ pre ([Pre , (K Mid) ] ;; [Mid , (K Post) ])); refine_simpl.
    intros s pres; exists pres; auto.
    eapply (Refinement _ _ d).
    refine_simpl; intros s x s' H; destruct H as [t q]; destruct q; auto.
  Qed.

Lemma refineSeqAssignPT : forall (f: S -> S) (g: S -> S) (h: S -> S),
  (forall (s : S), h s = g (f s)) -> 
  Assign_PT h ⊏ Assign_PT f ;; Assign_PT g.
Proof.
  intros.
  assert (d: pre (Assign_PT h) ⊂ pre (Assign_PT f ;; Assign_PT g)).
  unfold Assign_PT,Seq_PT,subset; simpl.
  intros; apply exist. 
  assumption. 
  intros; assumption.
  apply (Refinement _ _ d).
  simpl in *; unfold subset in *. 
  intros; inversion H0; inversion H1; rewrite H.
  rewrite <- x1; rewrite <- H2; reflexivity.
Qed.
  
Lemma seqExtendL (pt1 pt2 : PT) (U : Pow S) (s : S) : 
  extend pt1 (extend pt2 U) s -> extend (Seq_PT pt1 pt2) U s.
  Proof.
    refine_simpl.
    intro H; destruct H as [pres posts].
    exists (existT (fun pres => forall t, post pt1 s pres t -> pre pt2 t) pres 
             (fun t pt => projT1 (posts t pt))).
    unfold subset in *; simpl.
    intros s' H; destruct H as [s'' q]; destruct q as [H1 H2].
    apply (projT2 (posts s'' H1)); auto.
  Qed.

Lemma seqExtendR (pt1 pt2 : PT)  (U : Pow S) (s : S) : 
  extend (Seq_PT pt1 pt2) U s -> extend pt1 (extend pt2 U) s.
  Proof.
   unfold extend, subset; simpl; intro H; destruct H as [[pre1 pre2] post1].
   exists pre1.
   intros s' H; exists (pre2 s' H).
   intros s'' post3; apply (post1 s''); exists s'; exists H; exact post3.
  Qed.


(*** CONDITIONALS ***)

Definition Is_false (b : bool) :=
  match b with
    | true => False
    | false => True
  end.

Definition If_PT (cond : S -> bool) (Then Else : PT) : PT :=
  let ifPre := fun s => 
    prod (Is_true (cond s) -> pre Then s)
         (Is_false (cond s) -> pre Else s)
  in
  let ifPost := fun s pres s' => 
    prod (forall (p : Is_true (cond s)), post Then s (fst pres p) s') 
         (forall (p : Is_false (cond s)), post Else s (snd pres p) s')
  in
  [ ifPre , ifPost ].

Definition refineTransPT (pt2 pt1 pt3 : PT) : 
  pt1 ⊏ pt2 -> pt2 ⊏ pt3 -> pt1 ⊏ pt3.
    intros [pre12 post12] [pre23 post23].
    set (d (s : S) (pre1s : pre pt1 s) := pre23 s (pre12 s pre1s)).
    refine (Refinement pt1 pt3 d _).
    intros s pres s' post3.
    apply post12; apply post23; auto.
  Defined.

Definition refineReflPT (pt : PT) : pt ⊏ pt.
  refine (Refinement pt pt (fun s pres => pres) _).
  intros; unfold subset; auto.
  Defined.

Definition refineSplitPT (pt1 pt2 pt3 pt4 : PT) :
  (pt1 ⊏ pt3) -> (pt2 ⊏ pt4) -> (pt1 ;; pt2) ⊏ (pt3 ;; pt4).
    intros  [d1 f1] [d2 f2].
    set (d (s : S) (pres : pre (pt1;; pt2) s) :=
          existT (fun pres0 : pre pt3 s => forall t : S, post pt3 s pres0 t -> pre pt4 t)
          (d1 s (proj1_sig pres))
          (fun (t : S) (post2 : post pt3 s (d1 s (proj1_sig pres)) t) =>
            d2 t (proj2_sig pres t (f1 s (proj1_sig pres) t post2))) : pre (pt3;;pt4) s 
      ).
    apply (Refinement _ _ d).
    unfold d in *.
    simpl; intros s Pre s' [t [P Q]].
    exists t. exists (f1 s (proj1_sig Pre) t P).
    apply f2; auto.
  Defined.

Definition refineSplitIfPT (pt1 pt2 pt3 pt4 : PT) (cond : S -> bool) :
  (pt1 ⊏ pt3) -> (pt2 ⊏ pt4) -> If_PT cond pt1 pt2 ⊏ If_PT cond pt3 pt4.
  intros [d1 f1] [d2 f2].
  set (d (s : S) (X : pre (If_PT cond pt1 pt2) s)
         := (fun C : Is_true (cond s) => d1 s (fst X C),
             fun C : Is_false (cond s) => d2 s (snd X C)) 
            : pre (If_PT cond pt3 pt4) s).
  apply (Refinement _ _ d).    
  simpl; intros s pres s' [H1 H2].
  split; intros; [apply f1; apply H1 | apply f2; apply H2]; auto.
  Defined.

(* Law 5.1 *)
Lemma refineIfPT (cond : S -> bool) (pt : PT) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true (cond s)),
                     fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false (cond s)),
                     fun s pre s' => post pt s (fst pre) s' ] in
  
  pt ⊏ If_PT cond thenBranch elseBranch.
  Proof.
    intros.
    set (d (s : S) (X : pre pt s) := 
      (fun H : Is_true (cond s) => (X,H), fun H : Is_false (cond s) => (X,H))).
    apply (Refinement pt (If_PT cond thenBranch elseBranch) d).
    simpl; intros s pres s'; destruct (cond s); simpl; intros [H3 H4];  auto.
  Qed.


(* Law 5.1 *)
Lemma refineIfPT' (cond : S -> bool) (pt : PT) (PThen PElse : Pow S) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre PThen
                    , fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre PElse ,
                     fun s pre s' => post pt s (fst pre) s'  ] in
  let thenBranchBool := [branchPre (fun s => Is_true (cond s)), 
                                     (fun s pre s' => post pt s (fst pre) s')] in
  let elseBranchBool := [branchPre (fun s => Is_false (cond s)), 
                                   (fun s pre s' => post pt s (fst pre) s')] in
  (forall s : S, Is_true (cond s) -> PThen s) ->
  (forall s : S, Is_false (cond s) -> PElse s) ->
  pt ⊏ If_PT cond thenBranch elseBranch.
  Proof.
    intros.
    rename H into H1; rename H0 into H2.
    apply (refineTransPT (If_PT cond thenBranchBool elseBranchBool)).

    set (d (s : S) (X : pre pt s) := 
      (fun H : Is_true (cond s) => (X,H), fun H : Is_false (cond s) => (X,H))).
    apply (Refinement pt (If_PT cond thenBranchBool elseBranchBool) d).
    simpl; intros s pres s'; destruct (cond s); simpl; intros [H3 H4];  auto.

    apply refineSplitIfPT.
    set (d := (fun (s : S) (X : pre pt s * Is_true (cond s)) => 
                   (fst X,H1 s (snd X))) : pre thenBranchBool ⊂ pre thenBranch).
    apply (Refinement _ _ d).
    unfold subset; intros.
    simpl in *; assumption.

    set (d := (fun (s : S) (X : pre pt s * Is_false (cond s)) => 
                   (fst X,H2 s (snd X))) : pre elseBranchBool ⊂ pre elseBranch).
    apply (Refinement _ _ d).
    unfold subset; intros.
    simpl in *; assumption.
  Qed.

Lemma refineIfPT'' (cond : S -> bool) (pt : PT) (PThen PElse : Pow S) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [PThen , fun s pres s' => { HT : (pre pt s) & post pt s HT s'} ] in
  let elseBranch := [PElse , fun s pres s' => { HE : (pre pt s) & post pt s HE s'} ] in
  let thenBranchBool := [branchPre (fun s => Is_true (cond s)), 
                                   (fun s pres s' => { HT : (pre pt s) & post pt s HT s' &
                                                       post pt s (fst pres) s'})] in
  let elseBranchBool := [branchPre (fun s => Is_false (cond s)), 
                                   (fun s pre s' => post pt s (fst pre) s')] in
  (forall s : S, (branchPre (fun s => Is_true (cond s))) s -> PThen s) ->
  (forall s : S, (branchPre (fun s => Is_true (cond s))) s -> PElse s) ->
  pt ⊏ If_PT cond thenBranch elseBranch.
Proof.
  intros.
  apply (refineTransPT (If_PT cond thenBranchBool elseBranchBool)).
  set (d (s : S) (X : pre pt s) := 
      (fun H : Is_true (cond s) => (X,H), fun H : Is_false (cond s) => (X,H))).
  apply (Refinement pt (If_PT cond thenBranchBool elseBranchBool) d).
  simpl; intros s pres s'; destruct (cond s); simpl; intros [H3 H4]; auto.
Admitted.
  

Lemma IfExtendL (cond : S -> bool) (thenPt elsePt : PT) (U : Pow S) (s : S) :
  extend (If_PT cond thenPt elsePt) U s ->
    (Is_true (cond s) -> extend thenPt U s) * (Is_false (cond s) -> extend elsePt U s).
  Proof.
    unfold extend; simpl; destruct (cond s); simpl; split; try contradiction;
      unfold subset in *; simpl in *; destruct H as [[Pre1 Pre2] Post].
    intros; exists (Pre1 I);
      intros s' H'; apply Post; split; simpl; intros; destruct p; assumption.
    intros; exists (Pre2 I);
      intros s' H'; apply Post; split; simpl; intros; destruct p; assumption.
  Qed.

Lemma IfExtendR (cond : S -> bool) (thenPt elsePt : PT) (U : Pow S) (s : S) :
    (Is_true (cond s) -> extend thenPt U s) * (Is_false (cond s) -> extend elsePt U s) ->
    extend (If_PT cond thenPt elsePt) U s.
  Proof.
  unfold extend, subset. simpl; case (cond s); simpl; intros [H1 H2];
  exists (fun t => projT1 (H1 t) , fun f => projT1 (H2 f)).
    intros; apply (projT2 (H1 I)); destruct H as [A _]; apply A.
    intros; apply (projT2 (H2 I)); destruct H as [_ A]; apply A.
  Qed.

Definition While_PT (inv : Pow S) (cond : S -> bool) (body : PT) : PT :=
  let whilePre := (fun s =>   (* The invariant should hold initially *)
                             inv s /\ 
                              (* If we enter the loop, the precondition of the body should hold *)
                            { H : (forall s, Is_true (cond s) /\ inv s -> pre body s) &
                              (* The loop body should preserve the invariant *)
                            (forall s s' (t : Is_true (cond s) /\ inv s), post body s (H s t)  s' -> inv s')})                          
  in
  let whilePost := (fun _ _ s' => inv s' /\ Is_false (cond s')) in
  [ whilePre , whilePost ].

(* Law 7.1 *)
Lemma refineWhilePT (inv : Pow S) (cond : S -> bool) (Q : Pow S) : 
  let pt := [inv , fun _ _ s' => inv s' /\ Q s'] in
  let body := [fun s => inv s /\ Is_true (cond s), (fun _ _ s => inv s)] in
  (forall s, Is_false (cond s) -> Q s) ->
  pt ⊏ While_PT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (While_PT inv cond body)).
    unfold subset, pt,While_PT; simpl; intros; split; [assumption | ].
    split.
    intros s' H1. 
    destruct H1; split; assumption.
    intros s' s'' [H1 H2] H3; assumption.
    apply (Refinement _ _ d).
    intros s PreS s' [H1 H2].
    split; [ | apply QH]; assumption.
Qed.

Definition WhileSemantics  (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) : Type
  := inv s 
    /\ (forall s, Is_true (cond s) /\ inv s -> extend body inv s)
    /\ (forall s, Is_false (cond s) /\ inv s -> U s).

Lemma WhileExtendL (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) :
  extend (While_PT inv cond body) U s -> WhileSemantics inv cond body U s.
  Proof.
    unfold extend; simpl; intros [[H1 [H2 H3] H4 ]].
    split; [ assumption | split].
    - intros s' [H5 H6].
      unfold extend; exists (H2 s' (conj H5 H6)); intros s'' H7; eapply H3; exact H7.
    - intros s' [A B]; apply H4; split; try assumption.
  Qed.

Lemma WhileExtendR (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) :
  WhileSemantics inv cond body U s ->
    extend (While_PT inv cond body) U s.
  Proof.
    unfold extend; intros [I [T F]]; simpl in *.
    split; [split; [assumption | ] | ].
    set (H := fun s Hs => projT1 (T s Hs)); exists H.
    intros; eapply (projT2 (T s0 t)); unfold H in *; assumption.
    intros s' [H1 H2]; apply F; split; assumption.
Qed.

Lemma refineBodyPT : forall (inv : Pow S) (cond : S -> bool) (bodyL bodyR : PT),
  bodyL ⊏ bodyR ->
  While_PT inv cond bodyL ⊏ While_PT inv cond bodyR.
Proof.
  intros inv cond bodyL bodyR [Pre Post].
  assert (a: pre (While_PT inv cond bodyL) ⊂ pre (While_PT inv cond bodyR)).
  unfold subset; simpl; intros s [Inv [H1 H2]]; split.
  assumption.
  (* assert (E:  forall s0 : S, Is_true (cond s0) /\ inv s0 -> pre bodyR s0). *)
  set (E := fun s0 H => Pre s0 (H1 _ H)).
  exists E.
  intros s0 s' P Q.
  eapply H2.
  apply Post.
  unfold E in Q.
  exact Q.

  apply (Refinement _ _ a).
  intros.
  unfold post,subset,While_PT in *.
  simpl in *.
  intros; assumption.
Qed.

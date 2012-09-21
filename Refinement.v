 (* TODO: 
  - How to deal with allocation of vars? 
    Maybe its better to handle this from the outset
  - Total vs partial correctness. Should we worry about the 
    variant of a while?
  - How to handle frame rules? What can change and what cannot?
*)

Require Import List.
Require Import Bool.
Require Import Div2.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import String.

Section Refinement.

Record S : Type := mkS {varP : nat; varQ : nat; varR : nat}.

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

Notation "PT1 ⊑ PT2" := (Refines PT1 PT2) (at level 90) : type_scope.

Notation "[ p , q ]" := (Predicate p q) (at level 70) : type_scope.

Ltac refine_simpl := unfold subset, pre, post, extend; simpl; auto.

(*** Guarded command language ***)

Inductive Ty : Set := 
  | BOOL : Ty
  | INT : Ty.

(*** SKIP **)

Definition Skip : PT := 
  let skipPre := fun s => True in
  let skipPost := fun s pres s' => s = s' in
  [skipPre , skipPost].

(* Law 4.1 *)
Lemma refineSkip (pt : PT) : (forall s (pres : pre pt s), post pt s pres s) -> pt ⊑ Skip.
  Proof.
    intros H; assert (d : pre pt ⊂ pre Skip) by (unfold subset; simpl pre; auto).
    apply (Refinement pt Skip d).
    simpl subset; intros s pres s' eq; rewrite <- eq; auto.
  Qed.

Lemma SkipExtendL (U : Pow S) : extend Skip U ⊂ U.
  Proof.
    unfold extend; simpl subset; intros s [P1 P2]; apply P2; auto.
  Qed.

Lemma SkipExtendR (U : Pow S) : U ⊂ extend Skip U.
  Proof.
    unfold extend, subset; intros s Us; simpl; split; [trivial | intros s' eq; rewrite <- eq; now trivial].
  Qed.


(*** ASSIGNMENT ***)

Definition Assign : (S -> S) -> PT := fun f =>
  let assignPre := fun s => True in
  let assignPost := fun s _ s' => s' = f s in
  [assignPre , assignPost].

(* Law 1.3 *)
Lemma refineAssign (pt : PT) (f : S -> S) (h : forall (s : S) (pre : pre pt s), post pt s pre (f s)) 
  : pt ⊑ Assign f.
  Proof.
    assert (d : pre pt ⊂ pre (Assign f)); refine_simpl.
    eapply (Refinement pt (Assign f) d).
    simpl; intros s pres s' eq; rewrite eq; auto.
  Qed.

Lemma AssignExtendL (U : Pow S) (f : S -> S) (s : S) : extend (Assign f) U s -> U (f s).
  Proof.
    unfold extend; intros [H1 H2]; apply H2; reflexivity.
  Qed.

Lemma AssignExtendR  (U : Pow S) (f : S -> S) (s : S) : U (f s) -> extend (Assign f) U s.
  Proof.
    intros Ufs; unfold extend; simpl; split; [ trivial | unfold subset; intros s' eq; rewrite eq; now trivial].
  Qed.


(*** SEQUENCING **)

Definition Seq (pt1 pt2 : PT) : PT :=
  let seqPre := fun s => {pres : pre pt1 s | forall t, post pt1 s pres t -> pre pt2 t} in
  let seqPost : forall s : S, seqPre s -> Pow S := fun (s : S) (pres : seqPre s) (s' : S) => 
    exists t : S, exists q : post pt1 s (proj1_sig pres) t, post pt2 t (proj2_sig pres t q) s'
  in
  [seqPre , seqPost].

Notation "pt1 ;; pt2" := (Seq pt1 pt2) (at level 52, right associativity).

(* Law 4.2 *)
Lemma refineSeq (Pre Mid Post : Pow S) :
  let pt := [ Pre , fun _ _ s' => Post s' ] in
  pt ⊑ ([Pre , (fun _ _ s' => Mid s') ] ;; [Mid , (fun _ _ s' => Post s') ]).
  Proof.
    refine_simpl.
    assert (d : pre (Predicate Pre (K Post)) ⊂ pre ([Pre , (K Mid) ] ;; [Mid , (K Post) ])); refine_simpl.
    intros s pres; exists pres; auto.
    eapply (Refinement _ _ d).
    refine_simpl; intros s x s' H; destruct H as [t q]; destruct q; auto.
  Qed.

Lemma seqExtendL (pt1 pt2 : PT) (U : Pow S) (s : S) : 
  extend pt1 (extend pt2 U) s -> extend (Seq pt1 pt2) U s.
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
  extend (Seq pt1 pt2) U s -> extend pt1 (extend pt2 U) s.
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

Definition If (cond : S -> bool) (Then Else : PT) : PT :=
  let ifPre := fun s => 
    prod (Is_true (cond s) -> pre Then s)
         (Is_false (cond s) -> pre Else s)
  in
  let ifPost := fun s pres s' => 
    prod (forall (p : Is_true (cond s)), post Then s (fst pres p) s') 
         (forall (p : Is_false (cond s)), post Else s (snd pres p) s')
  in
  [ ifPre , ifPost ].

(* Law 5.1 *)
Lemma refineIf (cond : S -> bool) (pt : PT) : 
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true (cond s)) 
                    , fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false (cond s)) ,
                     fun s pre s' => post pt s (fst pre) s'  ] in
  
  pt ⊑ If cond thenBranch elseBranch.
  Proof.
    intros.
    set (d (s : S) (X : pre pt s) := 
      (fun H : Is_true (cond s) => (X,H), fun H : Is_false (cond s) => (X,H))).
    apply (Refinement pt (If cond thenBranch elseBranch) d).
    simpl; intros s pres s'; destruct (cond s); simpl; intros [H1 H2];  auto.
  Qed.

Lemma IfExtendL (cond : S -> bool) (thenPt elsePt : PT) (U : Pow S) (s : S) :
  extend (If cond thenPt elsePt) U s ->
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
    extend (If cond thenPt elsePt) U s.
  Proof.
  unfold extend, subset. simpl; case (cond s); simpl; intros [H1 H2];
  exists (fun t => projT1 (H1 t) , fun f => projT1 (H2 f)).
    intros; apply (projT2 (H1 I)); destruct H as [A _]; apply A.
    intros; apply (projT2 (H2 I)); destruct H as [_ A]; apply A.
  Qed.


Definition While (inv : Pow S) (cond : S -> bool) : PT :=
  let whilePre := fun s => inv s in
  let whilePost := fun s pres s' => prod (inv s') (Is_false (cond s')) in
  [ whilePre , whilePost ].

(* Law 7.1 *)
Lemma refineWhile (inv : Pow S) (cond : S -> bool) : 
  let pt := [inv , fun _ _ s' => prod (inv s') (Is_false (cond s')) ] in
  pt ⊑ While inv cond.
  Proof.
    intros; simpl in *.
    refine (Refinement _ _  (fun (s : S)(invs : pre pt s) => invs : pre (While inv cond) s) _).
    simpl; intros s pres s' ; auto.
  Qed.

Lemma WhileExtend (inv : Pow S) (cond : S -> bool) (U : Pow S) (s : S) :
  extend (While inv cond) U s -> 
    (inv s) * (forall s, (inv s * Is_false (cond s)) -> U s).
  Proof.
    unfold extend, subset; simpl; intros [I H]; split; auto. 
  Qed.

(*TODO WhileExtendL and WhileExtendR *)

Definition refineTrans (pt2 pt1 pt3 : PT) : 
  pt1 ⊑ pt2 -> pt2 ⊑ pt3 -> pt1 ⊑ pt3.
    intros [pre12 post12] [pre23 post23].
    set (d (s : S) (pre1s : pre pt1 s) := pre23 s (pre12 s pre1s)).
    refine (Refinement pt1 pt3 d _).
    intros s pres s' post3.
    apply post12; apply post23; auto.
  Defined.

Definition refineRefl (pt : PT) : pt ⊑ pt.
  refine (Refinement pt pt (fun s pres => pres) _).
  intros; unfold subset; auto.
  Defined.

Definition refineSplit (pt1 pt2 pt3 pt4 : PT) :
  (pt1 ⊑ pt3) -> (pt2 ⊑ pt4) -> (pt1 ;; pt2) ⊑ (pt3 ;; pt4).
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

Definition refineSplitIf (pt1 pt2 pt3 pt4 : PT) (cond : S -> bool) :
  (pt1 ⊑ pt3) -> (pt2 ⊑ pt4) -> If cond pt1 pt2 ⊑ If cond pt3 pt4.
  intros [d1 f1] [d2 f2].
  set (d (s : S) (X : pre (If cond pt1 pt2) s)
         := (fun C : Is_true (cond s) => d1 s (fst X C),
             fun C : Is_false (cond s) => d2 s (snd X C)) 
            : pre (If cond pt3 pt4) s).
  apply (Refinement _ _ d).    
  simpl; intros s pres s' [H1 H2].
  split; intros; [apply f1; apply H1 | apply f2; apply H2]; auto.
  Defined.



Definition setP : nat -> S -> S := fun x s =>
  match s with
    | mkS _ q r => mkS x q r
  end.

Definition setQ : nat -> S -> S := fun x s =>
  match s with
    | mkS p _ r => mkS p x r
  end.

Definition setR : nat -> S -> S := fun x s =>
  match s with
    | mkS p q _ => mkS p q x
  end.

Variable N : nat.

Definition square : nat -> nat := fun n => n * n.

Definition Inv : S -> Prop := fun X => square (varR X) <= N < square (varQ X).


Definition SPEC := 
  [ (fun _ => True), fun _ _ X => square (varR X) <= N < square (1 + varR X)].

Definition PT1 :=
  [ fun _ => True, fun _ _ X => Inv X /\ 1 + varR X = varQ X].

Ltac refine_post pt1 pt2 := apply (Refinement _ _ (fun s (y : pre pt1 s) => y : pre pt2 s)).

Lemma step1 : SPEC ⊑ PT1.
  Proof.
    unfold SPEC, PT1, Inv; refine_post SPEC PT1.
    intros X tt s [H1 H2]; simpl in *; rewrite H2; apply H1.
  Qed.

Definition PT2 := [fun _ => True , K Inv] ;; [Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X].

Lemma step2 : PT1 ⊑ PT2.
  Proof.
    unfold PT1, PT2, Inv, Seq; simpl.
    assert (d : forall s, pre PT1 s -> pre PT2 s).
    intros; exists I; intros; auto.
    apply (Refinement _ _ d).
    simpl; intros s Pre s' [t [H1 [H2 H3]]]; split; auto.
  Qed.

Definition PT3a :=
  Assign (fun s => mkS (varP s)  (1 + N) 0).

Definition PT3b :=
  While Inv (fun X => negb (beq_nat (1 + varR X) (varQ X))).

Lemma step3 : PT2 ⊑ (PT3a ;; PT3b).
  Proof.
   apply refineSplit.
   (* Part a *)
     unfold K, Inv, PT3a, square; apply refineAssign.
     simpl; intros; split; auto with arith.
   (* Part b *)
     unfold PT3b.
     assert (d : (pre ([Inv,fun _ _ X => Inv X /\ 1 + varR X = varQ X])) ⊂ pre PT3b).
     unfold subset; intros; auto.
     apply (Refinement _ _ d).
     intros s Pre s' [Post1 Post2]; split; auto.
     case_eq (beq_nat (Datatypes.S (varR s')) (varQ s')).
     intro H; apply (beq_nat_true (Datatypes.S (varR s')) (varQ s') H).
     change (Is_false (negb (beq_nat (Datatypes.S (varR s')) (varQ s')))) in Post2.
     intro F; rewrite F in Post2; contradiction.
 Qed.

Definition PT4 := 
  [fun X => 1 + varR X < varQ X, fun _ _ X => varR X < varP X < varQ X];;
  [fun X => varR X < varP X < varQ X /\ Inv X, fun _ _ X => Inv X].

Lemma step4 : PT3b ⊑ PT4.
  (* proceed by refining body of while? *)
  Admitted.
  

Definition PT5a :=
  Assign (fun s => setP (div2 (varQ s + varR s)) s).

Definition PT5bThen := 
  [fun s => (N < square (varP s)) /\ (varP s < varQ s) /\ Inv s,
   fun _ _ s' => Inv s'].

Definition PT5bElse :=
  [fun s => (N >= square (varP s)) /\ (varR s < varP s) /\ Inv s,
   fun _ _ s' => Inv s'].

Definition PT5b :=
  If (fun s => proj1_sig (nat_lt_ge_bool N (square (varP s))))
    PT5bThen PT5bElse.

Require Import Even.

Theorem even_even_lt_div2 : forall m n, even m /\ even n -> m < n -> div2 m < div2 n.
Proof.
  intros m n.
  generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. inversion H2.
    intros m H1 H2. destruct H1. inversion H0. inversion H3.
    intros n' H1 m H2 H3. simpl. generalize dependent m. intros m.
    apply ind_0_1_SS with (n:=m). intros H2 H3. apply lt_O_Sn. intros H2 H3. apply lt_O_Sn.
    intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3. split. inversion H.
    inversion H5. trivial. inversion H0. inversion H5. trivial. 
    repeat apply lt_S_n in H4. exact H4.
Qed.

Theorem even_plus_div2 : forall m n,
  even m -> div2 (m + n) = div2 m + div2 n.
Proof.
  intros m n.
  apply ind_0_1_SS with (n:=m).
    intros H. simpl. reflexivity.
    intros H. inversion H. inversion H1.
    intros x Hind H1. simpl. apply eq_S. apply Hind. inversion H1. inversion H0. trivial.
Qed.

Theorem even_odd_lt_div2 : forall m n, 
  even m /\ odd n -> Datatypes.S m < n -> div2 m < div2 n.
Proof.
  intros m n. generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. destruct H1 as [H3 H4]. inversion H4.
    intros m H1 H2. simpl. inversion H2. subst. inversion H0.
    intros n' H1 m H2 H3. simpl. generalize dependent m. intros m.
    apply ind_0_1_SS with (n:=m). intros H2 H3. simpl. apply lt_O_Sn.
    intros H2 H3. simpl. apply lt_O_Sn.
    intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H5 H6]. split. 
    inversion H5. inversion H0. trivial. inversion H6. inversion H0. trivial.
    repeat apply lt_S_n in H4. exact H4.
Qed.

Theorem odd_even_lt_div2 : forall m n,
  odd m /\ even n -> Datatypes.S m < n -> Datatypes.S (div2 m) < div2 n.
Proof.
  intros m.
  apply ind_0_1_SS with (n:=m). 
      intros n H1 H2. destruct H1 as [H1 H3]. inversion H1.
      intros n H1 H2. simpl. inversion H2. destruct H1 as [H1 H3]. rewrite <- H in H3.
      inversion H3. inversion H4. inversion H6. inversion H8.
      subst. destruct H1 as [H1 H3]. inversion H1. subst. inversion H. simpl. auto.
      subst. simpl. apply lt_n_S. inversion H0. simpl. auto. subst. inversion H5. simpl.
      auto. simpl. apply lt_O_Sn.
      intros n' H1 n H2 H3. simpl.
      generalize dependent n. intros n.
      apply ind_0_1_SS with (n:=n). intros H2 H3. inversion H3.
      intros H2 H3. inversion H3. inversion H0.
      intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H3 H5].
      split. inversion H3. inversion H0. trivial. inversion H5. inversion H0. trivial.
      repeat apply lt_S_n in H4. trivial.
Qed.     

Theorem odd_odd_plus_div2 : forall m n,
  odd m /\ odd n -> div2 (m + n) = Datatypes.S (div2 m + div2 n).
Proof.
  intros m n.
  apply ind_0_1_SS with (n:=m).
    intros H1. destruct H1 as [H1 H2]. inversion H1.
    apply ind_0_1_SS with (n:=n).
      intros H1. destruct H1 as [H1 H2]. inversion H2.
      intros H1. simpl. reflexivity.
      intros n' H1 H2. rewrite plus_comm. simpl. apply eq_S. rewrite plus_comm.
      apply H1. destruct H2 as [H2 H3]. split. trivial. inversion H3. inversion H0. trivial.
    intros x Hind H1. simpl. apply eq_S. apply Hind. destruct H1 as [H1 H2]. split.
    inversion H1. inversion H0. trivial. trivial.
Qed.

Theorem odd_odd_lt_div2 : forall m n,
  odd m /\ odd n -> m < n -> div2 m < div2 n.
Proof.
  intros m n. generalize dependent m.
  apply ind_0_1_SS with (n:=n).
    intros m H1 H2. inversion H2.
    intros m H1 H2. inversion H2. rewrite H0 in H1. destruct H1 as [H1 H3]. inversion H1.
    inversion H0.
    intros n' H1 m. apply ind_0_1_SS with (n:=m).
      intros H2 H3. destruct H2 as [H4 H5]. inversion H4.
      intros H2 H3. simpl. inversion H3. destruct H2 as [H2 H4]. 
      rewrite <- H0 in H4. inversion H4. inversion H5. inversion H7. apply lt_O_Sn.
      intros n'' H2 H3 H4. simpl. apply lt_n_S. apply H1. destruct H3 as [H3 H5].
      split. inversion H3. inversion H0. trivial. inversion H5. inversion H0. trivial.
      repeat apply lt_S_n in H4. exact H4.
Qed.

Lemma step5 : PT4 ⊑ (PT5a ;; PT5b).
  unfold PT4.
  unfold PT5a.
  unfold PT5b.
  simpl.
  apply refineSplit.
  apply refineAssign.
  simpl.
  intros s H.
  split.
  destruct s.
  simpl in *.

 (** even-odd approach **)
  assert (Ha: even varR0 \/ odd varR0).
  apply even_or_odd. destruct Ha as [R0even|R0odd].

  (* varR0 even *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].

  (* varR0 even, varQ0 even *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O.
  rewrite even_plus_div2. rewrite even_plus_div2. apply plus_lt_compat_r.
  apply even_even_lt_div2. split; trivial. apply le_Sn_le in H. exact H. trivial. trivial.

  (* varR0 even, varQ0 odd *)
  rewrite plus_comm. rewrite even_plus_div2. rewrite plus_comm. 
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  apply plus_lt_compat_r. apply even_odd_lt_div2. split; trivial. trivial. trivial. trivial.

  (* varR0 odd *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
  (* varR0 odd, varQ0 even *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite even_plus_div2. rewrite <- plus_Sn_m. apply plus_lt_compat_r. 
  apply odd_even_lt_div2. split; trivial. trivial. trivial. split; trivial.

  (* varR0 odd, varQ0 odd *)
  rewrite <- div2_double at 1. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite odd_odd_plus_div2. apply lt_n_S. apply plus_lt_compat_r. apply odd_odd_lt_div2. 
  split; trivial. apply le_Sn_le in H. trivial. split; trivial. split; trivial.
  (** end goal **)

  destruct s. simpl in *.

  (** even-odd approach **)
  assert (Ha: even varR0 \/ odd varR0). apply even_or_odd. destruct Ha as [R0even|R0odd].
  (* varR0 even *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
  (* varR0 even, varQ0 even *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  rewrite even_plus_div2. rewrite plus_comm. apply plus_lt_compat_r. 
  apply even_even_lt_div2. split; trivial. apply le_Sn_le in H. exact H. trivial. trivial.

  (* varR0 even, varQ0 odd *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite plus_comm. 
  rewrite even_plus_div2. rewrite odd_odd_plus_div2. rewrite <- plus_Sn_m. 
  apply plus_lt_compat_r. apply lt_S. apply even_odd_lt_div2. split; trivial. trivial. 
  split; trivial. trivial.

  (* varR0 odd *)
  assert (Ha: even varQ0 \/ odd varQ0). apply even_or_odd. destruct Ha as [Q0even|Q0odd].
  
  (* varR0 odd, varQ0 even *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite even_plus_div2. 
  rewrite even_plus_div2. rewrite plus_comm. apply plus_lt_compat_r. apply le_Sn_le. 
  apply odd_even_lt_div2. split; trivial. trivial. trivial. trivial.

  (* varR0 odd, varQ0 odd *)
  rewrite <- div2_double. unfold "*". rewrite <- plus_n_O. rewrite odd_odd_plus_div2. 
  rewrite odd_odd_plus_div2. apply lt_n_S. rewrite plus_comm. apply plus_lt_compat_r. 
  apply odd_odd_lt_div2. split; trivial. apply le_Sn_le in H. trivial. split; trivial. 
  split; trivial.
  (** end goal **)

  simpl. 
  Check refineIf.

Admitted.

Lemma step6Then : PT5bThen ⊑ Assign (fun s => setQ (varP s) s). 
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  destruct s. unfold Inv.
  simpl in *. destruct H3 as [H3 H4]. destruct H3.
  split; trivial. 
  simpl in *.
  split; auto.
Qed.

Lemma step6Else : PT5bElse ⊑ Assign (fun s => setR (varP s) s). 
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  destruct s. unfold Inv.
  simpl in *. destruct H3 as [H3 H4]. simpl in *.
  split; auto.
Qed.

(*
Theorem result : SPEC ⊑ 
  (
  PT3a ;; 
  While (PT5a ;; If (fun s => proj1_sig (nat_lt_ge_bool N (square (varP s))))
                   (Assign (fun s => setQ (varP s) s))
                   (Assign (fun s => setR (varP s) s)))
       (fun X => negb (beq_nat (1 + varR X) (varQ X)))
  ).
    apply (refineTrans PT1); try apply step1.
    apply (refineTrans PT2); try apply step2.
    apply (refineTrans (PT3a ;; PT3b)); try apply step3.
    apply refineRefl.  
Qed.
*)

(* Identifiers *) 

Inductive Identifier : Type :=
  | P : Identifier
  | Q : Identifier
  | R : Identifier.

Definition setIdent (ident: Identifier) : (nat -> S -> S) := (fun n => 
  match ident with
  | P => setP n
  | Q => setQ n
  | R => setR n
end).

Definition getIdent (ident: Identifier) : (S -> nat) := (fun s =>
  match ident , s with
  | P , mkS p _ _ => p
  | Q , mkS _ q _ => q
  | R , mkS _ _ r => r
end).

(* Expressions *)

Inductive Expr : Type :=
  | Var    : Identifier -> Expr
  | EConst : nat -> Expr
  | Plus   : Expr -> Expr -> Expr
  | Minus  : Expr -> Expr -> Expr
  | Mult   : Expr -> Expr -> Expr
  | Div    : Expr -> Expr -> Expr.

Inductive BExpr : Type :=
  | BConst : bool -> BExpr
  | And    : BExpr -> BExpr -> BExpr
  | Or     : BExpr -> BExpr -> BExpr
  | Eq     : Expr -> Expr -> BExpr
  | Lt     : Expr -> Expr -> BExpr
  | Le     : Expr -> Expr -> BExpr
  | Gt     : Expr -> Expr -> BExpr
  | Ge     : Expr -> Expr -> BExpr.

Fixpoint evalExpr (e: Expr) (s : S) : nat :=
  match e with
  | Var n     => (getIdent n) s
  | EConst n  => n
  | Plus x y  => evalExpr x s + evalExpr y s
  | Minus x y => evalExpr x s - evalExpr y s
  | Mult x y  => evalExpr x s * evalExpr y s
  | Div x y   => 0 (* FIXME *)
end.

(* TODO: finish this *)
Fixpoint evalBExpr (b: BExpr) (s: S) : bool :=
  match b with
  | BConst b  => b 
  | And b1 b2 => andb (evalBExpr b1 s) (evalBExpr b2 s) 
  | Or b1 b2  => true
  | Eq e1 e2  => true 
  | Lt e1 e2  => true
  | Le e1 e2  => true
  | Gt e1 e2  => true
  | Ge e1 e2  => true 
end.

(* While Language *)

Inductive WhileL : Type :=
  | WSkip   : WhileL
  | WAssign : Identifier -> Expr -> WhileL
  | WSeq    : WhileL -> WhileL -> WhileL
  | WIf     : BExpr -> WhileL -> WhileL -> WhileL
  | WWhile  : BExpr -> WhileL -> WhileL
  | WRef    : PT -> WhileL -> WhileL.

Fixpoint semantics (w: WhileL) : PT :=
  match w with
  | WSkip          => Skip
  | WAssign id exp => [(fun _ => True),(fun _ _ _ => True)] (*Assign ((setIdent id) (evalExpr exp))*)
  | WSeq st1 st2   => Seq (semantics st1) (semantics st2)
  | WIf c t e      => If (fun s => (evalBExpr c s)) (semantics t) (semantics e) (* fixme *)
  | WWhile c b     => [(fun _ => True),(fun _ _ _ => True)] (* TODO *)
  | WRef pt prg    => [(fun _ => True),(fun _ _ _ => True)] (* TODO *)
end.

Definition bp (b: BExpr) (s: S) : Prop := (evalBExpr b s) = true.

Fixpoint wp (w: WhileL) (post: Pow S) : Pow S :=
  match w with
  | WSkip          => post
  | WAssign id exp => (fun x => True)
  | WSeq st1 st2   => wp st1 (wp st2 post)
  | WIf c t e      => (bp c -> wp t post) /\ ((~ bp c) -> wp e post)
  | WWhile c b     => (fun x => True)
  | WRef pt prg    => (fun x => True)
end.

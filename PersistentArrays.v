Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Div2.
Require Import While.
Require Import Heap.
Require Import Refinement.
Require Import Program.Tactics.
Require Import Program.Equality.
Require Import Coq.omega.Omega.

(************************************************************

                PERSISTENT ARRAYS CASE-STUDY 

*************************************************************)


(** Some extra small automation **)

Hint Extern 2 =>
  match goal with
    | [ H1 : (find ?s ?p = Some ?v1), H2 : (find ?s ?p = None) |- _ ] => rewrite H1 in H2; inversion H2
    | [ H1 : (find ?s ?p = Some ?v1), H2 : (None = find ?s ?p) |- _ ] => rewrite H1 in H2; inversion H2
    | [ H1 : (Some ?v1 = find ?s ?p), H2 : (find ?s ?p = None) |- _ ] => rewrite H1 in H2; inversion H2
    | [ H1 : (Some ?v1 = find ?s ?p), H2 : (None = find ?s ?p) |- _ ] => rewrite H1 in H2; inversion H2
  end.

Hint Extern 2 (~ (_ = _)) => unfold not; intros; subst.

(*******************************************************************************
  **** Infrastructure following "A Persistent Union-Find Data Structure" ****
*******************************************************************************)

Set Implicit Arguments.
Require Export Wf_nat.

(* The possible data types present in the heap *)
Inductive PAData : Type :=
  | Arr : (nat -> nat) -> PAData
  | Diff : nat -> nat -> Ptr -> PAData
  | ResultGet : option nat -> PAData. (* used in the Get function *)

(* Updates an array at index i with v. *)
Definition upd (f : nat -> nat) (i : nat) (v : nat) := 
  fun j => if beq_nat j i then v else f j.

Hint Unfold upd.

(* 
   pa_model states that, given a pointer "p", we either have: 
   1. p points to an array "Arr", with elements given by (N -> N)
   2. p points to different "Diff", which is a change of another valid array,
      in one position only, updating the other array in that position (using upd)
*)
Inductive pa_model (s : heap PAData) : Ptr -> (nat -> nat) -> Type :=
  | pa_model_array :
     forall p f, find s p = Some ((Arr f)) -> pa_model s p f
  | pa_model_diff :
     forall p i v p', find s p = Some (Diff i v p') ->
                   forall f, pa_model s p' f ->
                        pa_model s p (upd f i v).

Hint Constructors PAData pa_model.

Lemma pa_model_find (s : heap PAData) (ptr : Ptr) (f : nat -> nat) :
    pa_model s ptr f -> { x : PAData & find s ptr = Some x }.
Proof. intros H; inversion H; subst; eauto. Qed.

Hint Resolve pa_model_find.

Lemma pa_model_find' (s : heap PAData) (ptr ptr' : Ptr) (f : nat -> nat) (i v : nat) :
    pa_model s ptr f -> find s ptr = Some (Diff i v ptr') -> { x : PAData & find s ptr' = Some x }.
Proof. intros H1 H2; inversion H1; subst; rewrite H2 in H; inversion H; subst; eauto. Qed.

Hint Resolve pa_model_find'.

(** Auxiliary lemmas about pa_model / upd. Taken from puf.v. **)

Axiom upd_ext : forall f g : nat -> nat, (forall i, f i = g i) -> f = g.

Lemma upd_eq : forall f i j v, i = j -> upd f i v j = v.
Proof. unfold upd; intros; subst; now rewrite Nat.eqb_refl. Qed. 

Lemma upd_eq_ext :
  forall f i v, f = upd (upd f i v) i (f i).
Proof.
  intros; apply upd_ext.
  intro i'; unfold upd; simpl.
  destruct (Nat.eq_dec i i'); subst. now rewrite <- beq_nat_refl.
  apply Nat.eqb_neq in n; rewrite Nat.eqb_sym in n; now rewrite n.
Qed.  

Lemma upd_fun : forall f f', f = f' -> forall i v, upd f i v = upd f' i v.
Proof. intros; rewrite H; reflexivity. Qed.

Hint Resolve upd_eq upd_eq_ext upd_fun.

Lemma pa_model_fun : forall s p f, pa_model s p f -> forall f', pa_model s p f' -> f = f'.
Proof.
  intros s ptr f HModel.
  induction HModel; intros f' HModel'; destruct HModel'; context_simpl; auto.
Qed.

(* Application of pa_model_diff when "f" does not directly read as an upd *)
Lemma pa_model_diff_2 :
  forall p : Ptr, forall i v p', forall f f' s,
  find s p = Some ((Diff i v p')) -> 
  pa_model s p' f' ->
  f = upd f' i v ->
  pa_model s p f. 
Proof. intros; subst; eauto. Qed.

(* Separation lemma: allocating a new pointer on the heap has no
   effect on existing PAs. *)
Lemma pa_model_sep' :
  forall s t f v t',
    find s t' = None -> 
    pa_model s t f -> pa_model (update s t' v) t f.
Proof.
  intros; generalize dependent t'.
  induction X; intros.
  - apply pa_model_array.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
  - apply pa_model_diff with (p' := p'); auto.
Qed.

Inductive PADataOpt : option PAData -> Prop :=
  | PAArr : forall f, PADataOpt (Some (Arr f))
  | PADiff : forall f i v, PADataOpt (Some (Diff f i v)).

Hint Constructors PADataOpt.

(* Separation lemma: a pointer that does not point to a structure
   of a PA, can be safely updated without affecting existing PAs  *)
Lemma pa_model_sep_padata :
  forall s t f v t',
    ~ (PADataOpt (find s t')) ->
    pa_model s t f -> pa_model (update s t' v) t f.
Proof.
  intros.
  intros; generalize dependent t'.
  induction X; intros.
  - apply pa_model_array.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst; rewrite e in H; auto.
  - apply pa_model_diff with (p' := p'); auto.
    apply findNUpdate1; auto.
    unfold not; intros; subst; rewrite e in H; auto.
Qed.

Lemma pa_model_alloc :
  forall s t' f v, pa_model s t' f -> pa_model (update s (alloc s) v) t' f.
Proof. intros; apply pa_model_sep'; auto. Qed.
  
(* decidability of find *)

Lemma find_eqdec : forall {A} s p, sumbool (find s p = None) (exists (c : A), find s p = Some c).
Proof. intros; destruct (find s p); eauto. Qed.

Lemma pa_model_copy_fresh :
  forall s p f, pa_model s p f -> forall v, find s p = Some v -> 
           forall t, (forall (p' : M.key) (x : PAData), find s p' = Some x -> p' <> t) ->
                pa_model (update s t v) t f.
Proof.
  intros s p f H1.
  induction H1; intros.
  - context_simpl; auto.
  - context_simpl. 
    eapply pa_model_diff with (p' := p'); auto.
    apply pa_model_sep'; auto.
    destruct (find_eqdec s t); auto.
    destruct e; apply H0 in H2; exfalso; auto.    
Qed.

Hint Resolve pa_model_fun pa_model_diff_2 pa_model_sep'
             pa_model_sep_padata pa_model_copy_fresh.

Hint Extern 2 =>
  match goal with
    | [ HH : (find ?s ?p = Some ?v1) +
            (find ?s ?p = Some ?v2) |- ~ PADataOpt (find ?s ?p) ] =>
      destruct HH as [HH | HH]; rewrite HH; unfold not; intro HInv; inversion HInv 
  end.

(*******************************************************************************
                            **** INIT ****
*******************************************************************************)

Definition initSpec (n : nat) (f : nat -> nat) : WhileL PAData Ptr := 
  Spec (MkPT (fun s => True)
                  (fun s pres v s' => prod (forall p' x, find s p' = Some x -> p' <> v)
                                          (pa_model s' v f))).

Definition newRef (x : PAData) : WhileL PAData Ptr :=
  New x (fun ptr => Return _ ptr).

Definition init (n : nat) (f : nat -> nat) : WhileL PAData Ptr := newRef (Arr f).

Lemma initRefinement : forall n f, wrefines (initSpec n f) (init n f).
Proof.
  intros.
  NEW (Arr f) t.
  RETURN t; eauto.
Qed.

(*******************************************************************************
                             **** SET ****
*******************************************************************************)

(* The original set implementation (i.e. no path compression), 
presented in Page 3 *)
Definition set (t : Ptr) (i : nat) (v : nat) : WhileL PAData Ptr :=
  Read t (fun vInT =>
  match vInT with
  | Arr f => New (Arr (upd f i v))
                (fun (res : Ptr) => Write t (Diff i (f i) res) (Return _ res))
  | Diff _ _ _ => newRef (Diff i v t)
  | _ => Return _ t (* absurd! *)                      
  end).

Definition setSpec (ptr : Ptr) (i : nat) (v : nat) : WhileL PAData Ptr :=
  Spec ( MkPT
   (fun s => { f : nat -> nat & pa_model s ptr f })
   (fun s pres newPtr s' => match pres with
                             | existT _ f _ => prod (pa_model s' newPtr (upd f i v))
                                                   (pa_model s' ptr f)
                           end )).

Lemma setRefinement : forall ptr i v, wrefines (setSpec ptr i v) (set ptr i v).
Proof.
  intros; unfold set, setSpec.
  READ ptr vInPtr.
  destruct vInPtr as [ f | j vInJ t' | ].
  - NEW (Arr (upd f i v)) res.
    WRITE ptr (Diff i (f i) res).
    RETURN res; inversion X; subst; context_simpl; eauto 6.
  - unfold newRef.
    NEW (Diff i v ptr) res.
    RETURN res. 
    apply pa_model_diff with (p' := ptr); auto. 
    apply pa_model_sep'; auto.
    destruct (find_eqdec pre res); auto; destruct e; exfalso; eapply n; eauto.
    apply pa_model_sep'; auto.
    destruct (find_eqdec pre res); auto; destruct e; exfalso; eapply n; eauto.
  - RETURN ptr; inversion X; subst; context_simpl.
Qed.

(*******************************************************************************
        **** Infrastructure for proving more elaborated functions ****
*******************************************************************************)

(* The list of pointers that together form a Persistent Array, hinting to
   a well-formed relation on pointers *)
Inductive dist (s : heap PAData) : Ptr -> list Ptr -> Type :=
  | dist_sing : forall p f, find s p = Some (Arr f) -> dist s p (p :: nil)
  | dist_cons : forall p p' i v l, 
                find s p = Some (Diff i v p') -> 
                dist s p' l -> dist s p (p :: l). 

Hint Constructors dist.

Inductive InT (p : Ptr) : list Ptr -> Type := 
  | here : forall l, InT p (p :: l)
  | there : forall p' l, InT p l -> InT p (p' :: l).

Hint Constructors InT.
  
Lemma dist_fun : forall s ptr l1, dist s ptr l1 -> forall l2, dist s ptr l2 -> l1 = l2.
Proof.
  intros s ptr l1 H.
  induction H; intros; inversion X; context_simpl; [ | apply f_equal ]; auto.
Qed.

Lemma dist_InT : forall s ptr l, dist s ptr l -> InT ptr l.
Proof. intros; induction X; auto. Qed.

Hint Resolve dist_fun dist_InT.

Lemma dist_sepT : forall s ptr l, dist s ptr l -> forall ptr', (InT ptr' l -> False) -> forall v, dist (update s ptr' v) ptr l.
Proof. intros s ptr l H; induction H; intros; [ | eapply dist_cons ]; eauto. Qed.    

Lemma pa_model_dist : forall s ptr f, pa_model s ptr f -> { l : list Ptr & dist s ptr l }.
Proof. intros; induction X; eauto. destruct IHX; eauto. Qed.

(* Separation lemma: if a pointer does not belong to the a given PA,
   then updating it should not affect that PA *)
Lemma pa_model_sep :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    (InT ptr' l -> False) ->
    pa_model (update s ptr' v) ptr f.
Proof.
  intros s f v ptr ptr' l HPA Hdist; generalize dependent ptr'; generalize dependent v; generalize dependent l.
  induction HPA; intros.
  - apply pa_model_array; rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_InT in Hdist; contradiction.
  - apply pa_model_diff with (p' := p').
    rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_InT in Hdist; contradiction.
    inversion Hdist; subst; rewrite e in H0; inversion H0; subst.    
    eapply IHHPA with (l := l0); auto.
Qed.

(* Separation lemma: if a pointer does not belong to the a given PA,
   then updating it to that PA should make it a PA as well *)
Lemma pa_model_sep_copy :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    (InT ptr' l -> False) -> 
    find s ptr = Some v -> 
    pa_model (update s ptr' v) ptr' f.
Proof.
  intros s f v ptr ptr' l HPA Hdist HFind; generalize dependent ptr'; generalize dependent v; generalize dependent l.
  induction HPA; intros; rewrite e in H.
  - apply pa_model_array; now rewrite findUpdate.
  - apply pa_model_diff with (p' := p').
    rewrite findUpdate; auto.
    assert (Ha : pa_model s p' f) by assumption.
    apply pa_model_dist in HPA.
    destruct HPA.
    eapply pa_model_sep; eauto.
    assert (Ha1 : l = p :: x) by eauto.
    inversion Hdist; rewrite e in H0; inversion H0; subst; eauto.
Qed.

Lemma dist_wf : forall s p1 l, dist s p1 l -> forall p2, p1 <> p2 -> InT p2 l ->
                      { l' : list Ptr & prod (dist s p2 l') (length l' < length l) }.
Proof.
  intros s p1 l Hdist p2 Heq HIn.
  destruct (M.E.eq_dec p1 p2); try contradiction.
  induction Hdist; intros.
  - inversion HIn; subst; exfalso; now apply n.
  - inversion HIn; subst.
    exfalso; now apply n.
    destruct (M.E.eq_dec p' p2); subst; eauto.
    assert ({l' : list Ptr & (dist s p2 l' * (Datatypes.length l' < Datatypes.length l))%type}).
    apply IHHdist; auto.
    destruct X as [x [H1 H2]]; eexists; split; eauto; simpl; omega.
Qed.

Lemma cons_contra : forall {A} (x : A) l, l <> x :: l.
Proof. intros; induction l; unfold not; intros HInv; inversion HInv; contradiction. Qed.
    
Lemma dist_no_loop : forall s p l, dist s p (p :: l) -> (InT p l -> False).
Proof.
  intros s p l H.
  dependent induction H.
  - unfold not; intros HInv; inversion HInv; subst.
  - unfold not; intros HH; subst.
    destruct (M.E.eq_dec p' p); subst.
    assert (Ha : l = p :: l).
    eapply dist_fun; eauto. eauto.
    assert (Ha : dist s p (p :: l)) by eauto.
    destruct (dist_wf H n HH) as [x [H1 H2]].
    assert (Ha1 : x = p :: l) by eauto.
    subst; simpl in *; omega.
Qed.

(* A pointer that points to a valid (Diff i v t'), 
   will still be valid when updated to whatever t' points to *)
Lemma pa_model_desc : forall s p1 f i v, pa_model s p1 (upd f i v) ->
                                    forall p2 v', pa_model s p2 f ->
                                             find s p1 = Some (Diff i v p2) ->
                                             find s p2 = Some v' ->
                                             pa_model (update s p1 v') p1 f.
Proof.
  intros s p1 f i v HP1 p2 v' HP2 HFind1 HFind2.
  assert (Ha : pa_model s p2 f) by assumption.
  apply pa_model_dist in HP2.
  destruct HP2.
  eapply pa_model_sep_copy; eauto.
  assert (Ha1 : pa_model s p1 (upd f i v)) by assumption.
  apply pa_model_dist in HP1.
  destruct HP1.
  assert (Ha2 : x0 = p1 :: x) by eauto.
  subst; eapply dist_no_loop; eassumption.
Qed.

(* Separation lemma: a pointer that does not point to a structure
   of a PA, can be safely updated without affecting existing PAs  *)
Lemma pa_dist_sep_padata :
  forall s t l v t',
    ~ (PADataOpt (find s t')) ->
    dist s t l -> dist (update s t' v) t l.
Proof.
  intros; generalize dependent t'.
  induction X; intros.
  - eapply dist_sing.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst; rewrite e in H; auto.
  - eapply dist_cons with (p' := p'); eauto 2.
    apply findNUpdate1; eauto 2.
    unfold not; intros; subst; rewrite e in H; eauto.
Qed.

Hint Resolve dist_sepT pa_model_dist pa_model_sep pa_model_sep_copy.
Hint Resolve pa_model_desc pa_dist_sep_padata.

(* If a pointer belongs to the indirection list of an array,
   it must point to a PADataOpt. *)
Lemma dist_InT_find_padata :
  forall ptr1 s l, dist s ptr1 l -> forall ptr2, InT ptr2 l -> PADataOpt (find s ptr2).
Proof.
  intros ptr1 s l Hdist.
  induction Hdist; intros ptr2 HInT; inversion HInT; subst; try (rewrite e; auto); eauto; inversion H0.
Qed.

(* If a pointer belongs to the indirection list of an array,
   it must point to a valid pointer in the heap *)
Lemma dist_InT_find : forall ptr1 s l, dist s ptr1 l -> forall ptr2, InT ptr2 l ->
                                  { v : PAData & find s ptr2 = Some v }.
Proof.
  intros ptr1 s l Hdist.
  induction Hdist; intros ptr2 HInT; inversion HInT; subst; eauto; inversion H0.
Qed.

Hint Resolve dist_InT_find dist_InT_find_padata.

(*******************************************************************************
                             **** GET ****
*******************************************************************************)

(* The original spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
*)

Definition data_get_eqb_some (h : option PAData) : bool :=
  match h with
    | Some (ResultGet (Some x)) => true
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

Definition getSpec (ptr : Ptr) (i : nat) : WhileL PAData nat :=
  Spec ( MkPT
   (fun s => { f : nat -> nat & pa_model s ptr f })
   (fun s pres v s' => match pres with
                        | existT _ f _ => v = f i
                      end )).  


(* Given the root pointer "ptr" and an auxiliary traversal pointer "t",
  "t" points to a persistent array (modelled by some f) such that:
   1. (f i) is the same as the function modelled by the original "ptr"
   2. the original array is read-only (i.e. out of the frame/scope)
   3. the result stored in "done" is either "None" or "Some (f i)" *)
Definition Inv ptr t done i si s :=
  { f : nat -> nat &
    (prod (pa_model s t f)
    (prod (forall f', pa_model si ptr f' -> prod (pa_model s ptr f') (f i = f' i)) (
    (prod ({ l : list Ptr & prod (dist s ptr l) (InT t l -> False)})
          (sum (find s done = Some (ResultGet (Some (f i))))
               (find s done = Some (ResultGet None))))))) }.

Definition get (ptr : Ptr) (i : nat) : WhileL PAData nat. 
refine (
  Read ptr (fun vInPtr =>
  New vInPtr (fun t =>
  New (ResultGet None) (fun done =>
  While (Inv ptr t done i)
        (fun s => negb (data_get_eqb_some (find s done)))
        (Read t (fun vInT => _ )) (* the body is refined below *)
        (Read done (fun vInDone =>
         match vInDone with
           | ResultGet (Some a) => Return _ a
           | _ => Return _ 0 (* absurd *)
         end)))))).
(* body of the loop *)
destruct vInT as [ f | j v t' | ].
refine (Write done (ResultGet (Some (f i))) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (ResultGet (Some v)) (Return _ tt)).
refine (Read t' (fun vInT' => Write t vInT' (Return _ tt))).
refine (Return _ tt). (* absurd: t will never point to a result *)
Defined.

Lemma getRefinement :  forall ptr i, wrefines (getSpec ptr i) (get ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  NEW vInPtr t.
  NEW (ResultGet None) done.
  WHILE (Inv ptr t done i) (fun s : S PAData => negb (data_get_eqb_some (find s done))); unfold Inv.
  - refine_simpl.
    exists s1.
    repeat split; auto.
    * apply pa_model_sep'; eauto. 
      destruct (find_eqdec (update s0 t vInPtr) done); eauto;
      destruct e; exfalso; eapply n; eauto.
    * assert (Ha1 : pa_model (update s0 t vInPtr) ptr s1).
      apply pa_model_sep_padata; auto.
      unfold not; intros H; inversion H; symmetry in H1; apply n0 in H1; now apply H1.
      assert (Ha2 : pa_model (update (update s0 t vInPtr) done (ResultGet None)) ptr s1).
      apply pa_model_sep'; auto.
      destruct (find_eqdec (update s0 t vInPtr) done); auto.
      destruct e; apply n in H; exfalso; auto.
      assert (Ha3 : s1 = f') by eauto; now rewrite Ha3.
    * assert (Ha : pa_model s0 ptr s1); auto.
      apply pa_model_dist in X0.
      destruct X0.
      exists x; split. 
      repeat apply dist_sepT; auto.
      + intro H; destruct (dist_InT_find d H) as [v HFind]; now apply (n0 _ _ HFind).
      + intro H; destruct (dist_InT_find d H) as [v HFind].
        rewrite <- findNUpdate with (p' := t) (v := vInPtr) in HFind.
        now apply (n _ _ HFind).
        unfold not; intros; subst; now apply (n0 _ _ HFind).
      + intro H; destruct (dist_InT_find d H) as [v HFind]; now apply (n0 _ _ HFind).
  - READ t vInT.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    destruct s3; eauto.
    RETURN tt.
    exists s1; repeat split; auto.
    * destruct (p0 _ X) as [Ha1 Ha2]; auto.
    * inversion p; rewrite H in e0; inversion e0; subst; now destruct (p0 _ X).
    * exists s2; split; auto.
    * rewrite findUpdate; left; repeat apply f_equal.
      inversion p; rewrite e0 in H; inversion H; now subst.
    * IFF (i =? n).
      + WRITE done (ResultGet (Some n0)).
        destruct s3; eauto.
        RETURN tt.
        eexists; split; eauto. 
        repeat split; intros.
        apply pa_model_sep_padata; auto; now destruct (p1 _ X).
        now destruct (p1 _ X).
        eauto.
        rewrite findUpdate; left; repeat apply f_equal.
        inversion p0; rewrite e0 in H; inversion H; subst. 
        unfold upd; now rewrite <- Heqb.
      + READ p vInT'.
        WRITE t vInT'.
        RETURN tt.
        inversion p0; subst; rewrite e1 in H; inversion H; subst; clear H.
        exists f0; repeat split.
        eauto 2.
        eapply pa_model_sep; eauto 2; now destruct (p1 _ X0).
        destruct (p1 _ X0); rewrite <- e; unfold upd; now rewrite <- Heqb. 
        exists s2; split; auto.
        destruct s3. 
        left; rewrite findNUpdate; eauto 1.
        rewrite e; repeat apply f_equal; unfold upd; now rewrite <- Heqb. 
        unfold not; intros; subst; rewrite e1 in e; inversion e.
        right; rewrite findNUpdate; eauto 1; unfold not; intros; subst;
        rewrite e1 in e; inversion e.
      * RETURN tt; inversion p; subst; rewrite e in H; inversion H.
  - READ done vInDone.
    destruct s3; eauto.
    destruct vInDone.
    * RETURN 0; rewrite e in i0; inversion i0.
    * RETURN 0; rewrite e in i0; inversion i0.
    * destruct o.
      + RETURN n.
        destruct s4.
        rewrite e0 in e; inversion e; subst.
        assert (Ha : (pa_model (update (update s5 t vInPtr) done (ResultGet None)) ptr s6)).
        apply pa_model_sep_padata.
        unfold not; intros HInv.
        destruct (find_eqdec (update s5 t vInPtr) done).
        rewrite e1 in HInv; inversion HInv.
        destruct e1;  apply n0 in H; now apply H.
        apply pa_model_sep'; auto.
        destruct (find_eqdec s5 t); [ | destruct e1; exfalso; apply n1 in H ]; auto.
        now destruct (p0 s6 Ha).
        rewrite e0 in e; inversion e.
      + RETURN 0; rewrite e in i0; inversion i0.
Qed.




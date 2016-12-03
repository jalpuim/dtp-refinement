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

(* Attempt following "A Persistent Union-Find Data Structure" *)

Set Implicit Arguments.
Require Export Wf_nat.

Inductive data : Type :=
  | Arr : (nat -> nat) -> data
  | Diff : nat -> nat -> Ptr -> data
  | ResultGet : option nat -> data
  | ResultFind : Ptr -> nat -> data.

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
  | _ => Return _ t (* absurd! *)                      
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

(* Main separation lemma *)
Lemma pa_model_sep' :
  forall s t f v t',
    find s t' = None -> 
    pa_model s t f -> pa_model (update s t' v) t f.
Proof.
  intros.
  intros; generalize dependent t'.
  induction X; intros.
  - apply pa_model_array.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst.
    rewrite H in e; inversion e.
  - apply pa_model_diff with (p' := p'); auto.
    apply findNUpdate1; auto.
    unfold not; intros; subst.
    rewrite H in e; inversion e.
Qed.

Inductive PAData : option data -> Prop :=
  | PAArr : forall f, PAData (Some (Arr f))
  | PADiff : forall f i v, PAData (Some (Diff f i v)).

Hint Constructors PAData.

(* Main separation lemma *)
Lemma pa_model_sep_padata :
  forall s t f v t',
    ~ (PAData (find s t')) ->
    pa_model s t f -> pa_model (update s t' v) t f.
Proof.
  intros.
  intros; generalize dependent t'.
  induction X; intros.
  - apply pa_model_array.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst.
    rewrite e in H; auto.
  - apply pa_model_diff with (p' := p'); auto.
    apply findNUpdate1; auto.
    unfold not; intros; subst.
    rewrite e in H; auto.
Qed.

Lemma pa_model_alloc :
  forall s t' f v, pa_model s t' f -> pa_model (update s (alloc s) v) t' f.
Proof.
  intros; apply pa_model_sep; auto; apply allocNotIn.
Qed.
  
(* decidability of find *)

Lemma find_eqdec : forall {A} s p, sumbool (find s p = None) (exists (c : A), find s p = Some c).
Proof. intros; destruct (find s p); eauto. Qed.

Lemma pa_model_copy :
  forall s p f, pa_model s p f -> forall v, find s p = Some v -> 
           forall t, (forall (p' : M.key) (x : data), find s p' = Some x -> p' <> t) ->
                pa_model (update s t v) t f.
Proof.
  intros s p f H1.
  induction H1; intros.
  - rewrite e in H; inversion H; subst.
    intros; apply pa_model_array; auto.
  - rewrite e in H; inversion H; subst.
    intros; eapply pa_model_diff with (p' := p'); auto.
    apply pa_model_sep'; auto.
    destruct (find_eqdec s t); auto.
    destruct e0; apply H0 in H2; exfalso; auto.    
Qed.
  
  
(** set refinement **)

Lemma setRefinement : forall ptr i v, wrefines (setSpec ptr i v) (set ptr i v).
Proof.
  intros; unfold set, setSpec.
  READ ptr vInPtr.
  inversion X0; eauto.
  destruct vInPtr as [ f | j vInJ t' | | ].
  - NEW (Arr (upd f i v)) res.
    inversion X; subst; rewrite H in e; inversion e.
    subst; exists f; apply pa_model_array; eauto.
    WRITE ptr (Diff i (f i) res).
    RETURN res.
    inversion X; subst; rewrite H in e1; inversion e1.
    subst; clear e1.
    apply pa_model_array.
    erewrite findNUpdate1 with (x := Some (Arr (upd f i v))); auto.
    unfold not; intros; subst; apply n in H; now apply H.
    inversion X; subst; rewrite H in e1; inversion e1.
    subst; clear e1.
    apply pa_model_diff_2 with (i := i) (v := f i) (p := ptr) (p' := res)
                                       (f' := upd f i v); auto.
    apply pa_model_array; eauto.
    apply upd_eq_ext.
  - unfold newRef; NEW (Diff i v ptr) res.
    inversion X; subst; rewrite H in e; inversion e.
    subst; clear e.
    exists (upd f j vInJ).
    apply pa_model_diff with (p := ptr) (p' := t'); eauto.
    now apply pa_model_alloc.
    RETURN res.
    apply pa_model_diff with (p' := ptr); auto.
    apply someIn in e0; apply pa_model_sep'; auto.
    destruct (find_eqdec pre res); auto.
    destruct e; exfalso; eapply n; eauto.
    apply someIn in e0; apply pa_model_sep'; auto.
    destruct (find_eqdec pre res); auto.
    destruct e; exfalso; eapply n; eauto.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
    auto.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
    auto.
Qed.

(*** GET ***)
(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
*)

Definition data_get_eqb_some (h : option data) : bool :=
  match h with
    | Some (ResultGet (Some x)) => true
    | _ => false
  end.

Lemma get_eqb_dec :
  forall d, sumbool (data_get_eqb_some d = true) (data_get_eqb_some d = false).
Proof.
  intros d; destruct d; unfold data_get_eqb_some; simpl; auto.
  destruct d; auto; destruct o; auto.
Qed.

Definition isSome (h : option data) : bool :=
  match h with
    | Some _ => true
    | None => false
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

Definition get (ptr : Ptr) (i : nat) : WhileL data nat.
refine (
  Read ptr (fun vInPtr =>
  New vInPtr (fun t =>
  New (ResultGet None) (fun done =>
  While (fun s' s => prod ({ f : nat -> nat & pa_model s t f })
                  (prod (t <> done) ({ x : option nat & find s done = Some (ResultGet x) })))
        (fun s => negb (data_get_eqb_some (find s done)))
        (Read t (fun vInT => _ )) (* the body is refined below *)
        (Read done (fun vInDone =>
         match vInDone with
           | ResultGet (Some a) => Return _ a
           | _ => Return _ 0 (* absurd *)
         end)))))).
(* body of the loop *)
destruct vInT as [ f | j v t' | | ].
refine (Write done (ResultGet (Some (f i))) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (ResultGet (Some v)) (Return _ tt)).
refine (Read t' (fun vInT' => Write t vInT' (Return _ tt))).
refine (Return _ tt). (* absurd: t will never point to a result *)
refine (Return _ tt). (* absurd: t will never point to a result *)
Defined.

(* The adapted spec from Ch.4 *)
(*
Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
 *)
Definition getSpec : Ptr -> nat -> WhileL data nat.
  intros ptr i.
  refine (Spec _). 
  refine (Predicate (fun s => { f : nat -> nat & pa_model s ptr f}) _).
  intros s [f H] v.
  refine (fun s' => v = f i).
Defined.

Hint Constructors pa_model.
Hint Resolve pa_model_alloc pa_model_sep.



(* STARTS HERE: new get *)

Inductive dist (s : heap data) : Ptr -> list Ptr -> Type :=
  | dist_sing : forall p f, find s p = Some (Arr f) -> dist s p (p :: nil)
  | dist_cons : forall p p' i v l, 
                find s p = Some (Diff i v p') -> 
                dist s p' l -> dist s p (p :: l). 

Hint Constructors dist.
Hint Unfold List.In.

Inductive InT (p : Ptr) : list Ptr -> Type := 
  | here : forall l, InT p (p :: l)
  | there : forall p' l, InT p l -> InT p (p' :: l).

Hint Constructors InT.

Lemma InT_to_In : forall p l, InT p l -> In p l.
Proof. intros. induction l. inversion H. inversion H; subst; auto. right; auto. Qed.
  
Lemma dist_fun : forall s ptr l1, dist s ptr l1 -> forall l2, dist s ptr l2 -> l1 = l2.
Proof.
  intros s ptr l1 H.
  induction H; intros.
  - inversion X; subst; auto.
    rewrite e in H; inversion H.
  - inversion X; subst; rewrite e in H0; inversion H0; subst.
    apply f_equal; auto.
Qed.

Lemma dist_In : forall s ptr l, dist s ptr l -> List.In ptr l.
Proof. intros; induction X; auto. Qed.

Lemma dist_InT : forall s ptr l, dist s ptr l -> InT ptr l.
Proof. intros; induction X; auto. Qed.

Lemma dist_sep : forall s ptr l, dist s ptr l -> forall ptr', ~ List.In ptr' l -> forall v, dist (update s ptr' v) ptr l.
Proof.
  intros s ptr l H.
  induction H; intros.
  - simpl; apply dist_sing with (f := f); rewrite findNUpdate; auto.
  - eapply dist_cons.
    erewrite findNUpdate; eauto 5.
    apply IHdist; unfold not; intros HH; apply H0; now right.
Qed.


Lemma dist_sepT : forall s ptr l, dist s ptr l -> forall ptr', (InT ptr' l -> False) -> forall v, dist (update s ptr' v) ptr l.
Proof.
  intros s ptr l H.
  induction H; intros.
  - simpl; apply dist_sing with (f := f); rewrite findNUpdate; auto.
    unfold not; intros HH; subst.
    apply H; auto.
  - eapply dist_cons.
    erewrite findNUpdate; eauto 2.
    unfold not; intros HH; subst.
    apply H0; auto.
    apply IHdist; unfold not; intros HH; apply H0; now right.
Qed.

Lemma dist_sep2 : forall s ptr ptr' l v, dist (update s ptr' v) ptr l -> ~ List.In ptr' l -> dist s ptr l.
Proof.
  intros s ptr ptr' l v H.
  dependent induction H; intros.
  - eapply dist_sing.
    erewrite <- findNUpdate.
    eapply e.
    auto.
  - eapply dist_cons.
    erewrite <- findNUpdate; eauto 5.
    apply IHdist; unfold not; intros HH; apply H0; now right.
Qed. 
    

Lemma pa_model_dist : forall s ptr f, pa_model s ptr f -> { l : list Ptr & dist s ptr l }.
Proof. intros; induction X; eauto. destruct IHX; eauto. Qed.

Lemma pa_model_sep_ugly :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    ~ List.In ptr' l ->
    pa_model (update s ptr' v) ptr f.
Proof.
  intros s f v ptr ptr' l HPA Hdist. generalize dependent ptr'. generalize dependent v. generalize dependent l.
  induction HPA; intros.
  - apply pa_model_array.
    rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_In in Hdist.
    contradiction.
  - apply pa_model_diff with (p' := p').
    rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_In in Hdist; contradiction.
    inversion Hdist; subst; rewrite e in H0; inversion H0; subst.    
    eapply IHHPA with (l := l0); auto.
Qed.

Lemma pa_model_sep_uglyT :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    (InT ptr' l -> False) ->
    pa_model (update s ptr' v) ptr f.
Proof.
  intros s f v ptr ptr' l HPA Hdist. generalize dependent ptr'. generalize dependent v. generalize dependent l.
  induction HPA; intros.
  - apply pa_model_array.
    rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_InT in Hdist.
    contradiction.
  - apply pa_model_diff with (p' := p').
    rewrite findNUpdate; auto.
    unfold not; intros; subst.
    apply dist_InT in Hdist; contradiction.
    inversion Hdist; subst; rewrite e in H0; inversion H0; subst.    
    eapply IHHPA with (l := l0); auto.
Qed.

Lemma pa_model_sep_ugly2 :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    ~ List.In ptr' l ->
    find s ptr = Some v -> 
    pa_model (update s ptr' v) ptr' f.
Proof.
  intros s f v ptr ptr' l HPA Hdist HFind. generalize dependent ptr'. generalize dependent v. generalize dependent l.
  induction HPA; intros.
  - apply pa_model_array; rewrite e in H; now rewrite findUpdate.
  - rewrite e in H.
    apply pa_model_diff with (p' := p'). 
    rewrite findUpdate; auto.
    assert (Ha : pa_model s p' f) by assumption.
    apply pa_model_dist in HPA.
    destruct HPA.
    eapply pa_model_sep_ugly. auto.
    apply d.
    assert (Ha1 : l = p :: x).
    inversion Hdist; subst; rewrite e in H0; inversion H0; subst.
    apply f_equal.
    eapply dist_fun; eauto.
    subst.
    unfold not; intros; apply HFind.
    now right.
Qed.

Lemma pa_model_sep_ugly2T :
  forall s f v ptr ptr' l,
    pa_model s ptr f ->
    dist s ptr l ->
    (InT ptr' l -> False) -> 
    find s ptr = Some v -> 
    pa_model (update s ptr' v) ptr' f.
Proof.
  intros s f v ptr ptr' l HPA Hdist HFind. generalize dependent ptr'. generalize dependent v. generalize dependent l.
  induction HPA; intros.
  - apply pa_model_array; rewrite e in H; now rewrite findUpdate.
  - rewrite e in H.
    apply pa_model_diff with (p' := p'). 
    rewrite findUpdate; auto.
    assert (Ha : pa_model s p' f) by assumption.
    apply pa_model_dist in HPA.
    destruct HPA.
    eapply pa_model_sep_uglyT. auto.
    apply d.
    assert (Ha1 : l = p :: x).
    inversion Hdist; subst; rewrite e in H0; inversion H0; subst.
    apply f_equal.
    eapply dist_fun; eauto.
    subst.
    unfold not; intros; apply HFind.
    auto.
Qed.

Lemma bar : forall s p1 l, dist s p1 l -> forall p2, p1 <> p2 -> InT p2 l -> { l' : list Ptr & prod (dist s p2 l') (length l' < length l) }.
Proof.
  intros s p1 l Hdist p2 Heq HIn.
  destruct (M.E.eq_dec p1 p2).
  contradiction.
  induction Hdist; intros.
  - inversion HIn; subst; exfalso; now apply n.
  - inversion HIn; subst.
    exfalso; now apply n.
    destruct (M.E.eq_dec p' p2); subst; eauto.
    assert ({l' : list Ptr & (dist s p2 l' * (Datatypes.length l' < Datatypes.length l))%type}).
    apply IHHdist; auto.
    destruct X.
    exists x.
    destruct p0; split; auto.
    simpl.
    now apply Nat.lt_lt_succ_r.
Qed.

Lemma cons_contra : forall {A} (x : A) l, l <> x :: l.
Proof.
  intros.
  induction l.
  - unfold not; intros HInv; inversion HInv.
  - unfold not; intros HInv; inversion HInv; contradiction.
Qed.
    
Lemma foo : forall s p l, dist s p (p :: l) -> (InT p l -> False).
Proof.
  intros s p l H.
  dependent induction H.
  - unfold not; intros HInv; inversion HInv; subst.
  - unfold not; intros HH; subst.
    destruct (M.E.eq_dec p' p).
    subst.
    assert (Ha : l = p :: l).
    eapply dist_fun; eauto.
    eapply cons_contra; apply Ha. 
    assert (Ha : dist s p (p :: l)) by eauto.
    destruct (bar H n HH).
    destruct p0.
    assert (Ha1 : x = p :: l).
    eapply dist_fun; eauto.
    subst.
    simpl in l0.
    eapply Nat.nlt_succ_diag_l; apply l0.
Qed.
  
Lemma pa_model_desc : forall s p1 f i v, pa_model s p1 (upd f i v) ->
                                    forall p2 v', pa_model s p2 f -> find s p1 = Some (Diff i v p2) -> find s p2 = Some v' ->
                                             pa_model (update s p1 v') p1 f.
Proof.
  intros s p1 f i v HP1 p2 v' HP2 HFind1 HFind2.
  assert (Ha : pa_model s p2 f) by assumption.
  apply pa_model_dist in HP2.
  destruct HP2.
  eapply pa_model_sep_ugly2T; eauto.

  assert (Ha1 : pa_model s p1 (upd f i v)) by assumption.
  apply pa_model_dist in HP1.
  destruct HP1.
  assert (Ha2 : x0 = p1 :: x).
  inversion d0; subst.
  inversion d0; subst.
  rewrite H0 in HFind1; inversion HFind1.
  inversion X.
  rewrite H in HFind1; inversion HFind1; subst.
  apply f_equal.
  eapply dist_fun; eauto.
  subst.
  eapply foo. apply d0.
Qed.

Inductive ForallT (A : Type) (P : A -> Type) : list A -> Type :=
    ForallT_nil : ForallT P nil
  | ForallT_cons : forall (x : A) (l : list A),
                     P x -> ForallT P l -> ForallT P (x :: l).

Hint Constructors ForallT.

Lemma upd_fun : forall f f', f = f' -> forall i v, upd f i v = upd f' i v.
Proof. intros; rewrite H; reflexivity. Qed.

Lemma pa_model_fun : forall s p f, pa_model s p f -> forall f', pa_model s p f' -> f = f'.
Proof.
  intros s ptr f HModel.
  induction HModel; intros f' HModel'.
  - destruct HModel'; rewrite e0 in e; inversion e; now subst.
  - destruct HModel'; rewrite e0 in e; inversion e; subst.
    apply upd_fun.
    auto.
Qed.

Lemma pa_model_dist_eq :
  forall s ptr f l, pa_model s ptr f -> dist s ptr l ->
               forall s', ForallT (fun p' => find s p' = find s' p') l ->
                     pa_model s' ptr f.
Proof.
  intros s ptr f l HModel HDist s' HForall.
  generalize dependent s'. generalize dependent l.
  induction HModel; intros.
  - inversion HDist; subst; rewrite e in H; inversion H; subst; clear H.
    inversion HForall; subst.
    apply pa_model_array; rewrite <- e; auto.
  - inversion HDist; subst; rewrite e in H; inversion H; subst; clear H.
    inversion HForall; subst.
    eapply pa_model_diff. rewrite <- e; eauto. 
    eapply IHHModel.
    apply X.
    auto.
Qed.

Lemma pa_dist_sep_padata :
  forall s t l v t',
    ~ (PAData (find s t')) ->
    dist s t l -> dist (update s t' v) t l.
Proof.
  intros.
  intros; generalize dependent t'.
  induction X; intros.
  - eapply dist_sing.
    rewrite findNUpdate1 with (x := Some ((Arr f))); auto.
    unfold not; intros; subst.
    rewrite e in H; auto.
  - eapply dist_cons with (p' := p'); eauto.
    apply findNUpdate1; auto.
    unfold not; intros; subst.
    rewrite e in H; eauto.
    apply e.
Qed.


(***** Latest changes ******)

Definition Inv ptr t done i si s :=
  { f : nat -> nat & (prod (pa_model s t f)
                      (prod (forall f, pa_model si ptr f -> pa_model s ptr f) (
                      (prod ({ l : list Ptr & prod (dist s ptr l) (InT t l -> False)})
                            (prod
                               (sum (find s done = Some (ResultGet (Some (f i))))
                                    (find s done = Some (ResultGet None)))
                               ({ f' : nat -> nat & (prod (pa_model s ptr f')
                                                     (f i = f' i))}))))))}.

Definition getNewInvUgly (ptr : Ptr) (i : nat) : WhileL data nat. 
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
destruct vInT as [ f | j v t' | | ].
refine (Write done (ResultGet (Some (f i))) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (ResultGet (Some v)) (Return _ tt)).
refine (Read t' (fun vInT' => Write t vInT' (Return _ tt))).
refine (Return _ tt). (* absurd: t will never point to a result *)
refine (Return _ tt). (* absurd: t will never point to a result *)
Defined.

(* get (using a loop) refinement *)
Lemma getRefinementNewInvUgly' :  forall ptr i, wrefines (getSpec ptr i) (getNewInvUgly ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  apply newSpec'; intro t.
  apply newSpec'; intro done.
  apply whileSpec.
  - refine_simpl.
    unfold Inv.
    exists s1.
    repeat split; auto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H; symmetry in H1; apply n in H1; now apply H1.
    apply pa_model_copy with (p := ptr); auto.
    assert (Ha : pa_model s0 ptr s1); auto.
    apply pa_model_dist in X0.
    destruct X0.
    exists x.
    split. apply dist_sepT.
    apply dist_sepT; auto.
    
    unfold not; intros.
    clear e1 Ha.
    induction d; subst. 
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.

    unfold not; intros.
    clear e1 Ha.
    induction d; subst.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    inversion H1.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    auto.
    
    unfold not; intros.
    clear e1 Ha.
    induction d; subst.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.

    exists s1.
    split; auto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H; symmetry in H1; apply n in H1; now apply H1.
    apply pa_model_sep'; auto.
    destruct (find_eqdec s0 t); auto.
    destruct e; apply n0 in H; exfalso; auto.
  - unfold Inv.
    READ t vInT.
    inversion p; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    destruct s3; eauto.
    RETURN tt; eauto.
    eexists; repeat split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros HInv.
    destruct s3; rewrite e in HInv; inversion HInv.
    eauto.
    intros.
    assert (Ha := p0 _ X).
    apply pa_model_sep_padata; auto.
    unfold not; intros HInv.
    destruct s3; rewrite e in HInv; inversion HInv.
    exists s2.
    split; auto.
    apply pa_dist_sep_padata; auto.
    unfold not; intros HInv; destruct s3; rewrite e in HInv; inversion HInv.
    exists s4.
    split; auto.
    apply pa_model_sep_padata; auto.
    unfold not; intros HInv.
    destruct s3; rewrite e in HInv; inversion HInv.
    rewrite <- e1.
    inversion p; subst; rewrite e0 in H; inversion H; now subst.

    destruct (Nat.eq_dec i n).
    subst.
    rewrite PeanoNat.Nat.eqb_refl.
    WRITE done (ResultGet (Some n0)).
    destruct s3; eauto.
    RETURN tt; eauto.
    eexists; split; eauto. 
    apply pa_model_sep_padata; eauto.
    unfold not; intros HInv.
    destruct s3; auto; rewrite e in HInv; inversion HInv.
    destruct s3; rewrite e in i.
    exfalso; auto; simpl in i.
    split.
    intros.
    apply pa_model_sep_padata; auto.
    unfold not; intros HInv; rewrite e in HInv; inversion HInv.
    split.
    exists s2.
    split.
    apply dist_sepT; auto.

    clear p0 p1 p2.
    unfold not; intros.
    induction d; subst.
    inversion H; subst.
    rewrite e in e2; inversion e2.
    inversion H1.
    inversion H; subst.
    rewrite e in e2; inversion e2.
    apply IHd.
    intros; apply f; auto.
    auto.

    auto.
    split.
    left; rewrite findUpdate; repeat apply f_equal.
    inversion p0; rewrite H in e0; inversion e0; subst.
    unfold upd; now rewrite <- beq_nat_refl.
    exists s4; split; auto.
    apply pa_model_sep_padata; auto.
    rewrite e; unfold not; intros HInv; inversion HInv.

    
    apply Nat.eqb_neq in n1.
    rewrite n1.
    READ p vInT'.
    inversion p0; subst; rewrite e in H; inversion H; subst.
    inversion X; subst; eauto.
    WRITE t vInT'.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e1 in H; inversion H; subst; clear H.
    exists f0.
    repeat split.
    eapply pa_model_desc; eauto.
    intros.
    eapply pa_model_sep_uglyT; eauto.
    exists s2.
    split; auto; apply dist_sepT; auto.
    destruct s3; auto.
    left. rewrite findNUpdate; eauto 1. rewrite e. repeat apply f_equal. unfold upd; now rewrite n1.
    unfold not; intros; subst; rewrite e1 in e; inversion e.
    right; rewrite findNUpdate; eauto 1; unfold not; intros; subst; rewrite e1 in e; inversion e.
    exists s4. split; auto.
    assert (Ha : pa_model pre ptr s4) by assumption.
    apply pa_model_dist in Ha; destruct Ha.
    eapply pa_model_sep_uglyT; eauto.
    assert (Ha : x = s2) by (eapply dist_fun; eauto). subst.
    auto.
    rewrite <- e2.
    unfold upd; now rewrite n1.
    RETURN tt; eauto.
    inversion p; subst; rewrite e in H; inversion H.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e in H; inversion H.
  - unfold Inv.
    READ done vInDone.
    destruct s3; eauto.
    destruct vInDone.
    RETURN 0.
    rewrite e in i0.
    inversion i0.
    RETURN 0.
    rewrite e in i0; inversion i0.
    destruct o.
    RETURN n.
    destruct s4.
    rewrite e1 in e.
    inversion e.
    subst.
    rewrite e0.
    assert (Ha : (pa_model (update (update s6 t vInPtr) done (ResultGet None)) ptr s7)).
    apply pa_model_sep_padata.
    unfold not; intros HInv.
    destruct (find_eqdec (update s6 t vInPtr) done).
    rewrite e2 in HInv; inversion HInv.
    destruct e2.
    apply n0 in H.
    now apply H.
    apply pa_model_sep'.
    destruct (find_eqdec s6 t).
    apply e2.
    destruct e2.
    exfalso; apply n1 in H; now apply H.
    assumption.
    pose (p0 s7).
    apply p2 in Ha.
    assert (s5 = s7). eapply pa_model_fun; eauto.
    now rewrite H.
    rewrite e1 in e.
    inversion e.
    RETURN 0.
    rewrite e in i0.
    simpl in i0.
    exfalso; assumption.
    RETURN 0.
    rewrite e in i0.
    simpl in i0.
    exfalso; assumption.
Qed.
    
(***** ******)

Definition Inv ptr t done i s := { f : nat -> nat & (prod (pa_model s t f)
                                 (prod ({ l : list Ptr & prod (dist s ptr l) (InT t l -> False)})
                                 (prod
                                (sum (find s done = Some (ResultGet (Some (f i))))
                                     (find s done = Some (ResultGet None)))
                                ({ f' : nat -> nat & (prod (pa_model s ptr f')
                                                      (f i = f' i))}))))}.

Definition getNewInvUgly (ptr : Ptr) (i : nat) : WhileL data nat. 
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
destruct vInT as [ f | j v t' | | ].
refine (Write done (ResultGet (Some (f i))) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (ResultGet (Some v)) (Return _ tt)).
refine (Read t' (fun vInT' => Write t vInT' (Return _ tt))).
refine (Return _ tt). (* absurd: t will never point to a result *)
refine (Return _ tt). (* absurd: t will never point to a result *)
Defined.

(* get (using a loop) refinement *)
Lemma getRefinementNewInvUgly' :  forall ptr i, wrefines (getSpec ptr i) (getNewInvUgly ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  apply newSpec'; intro t.
  apply newSpec'; intro done.
  eapply refineWhile
  with (w1 := Predicate (fun s => Inv ptr t done i s)
                       (fun ss pres v s => prod (Inv ptr t done i s)
                       (forall l, dist ss ptr l -> ForallT (fun p' => find ss p' = find s p') l)))
         (w2 := Predicate (fun s => Inv ptr t done i s)
                         (fun ss pres v s => (projT1 pres) i = v)).
  simpl.

  eapply (Refinement _ _ _ _).
  Unshelve.
  Focus 3.
  
(*  
  assert (d : subset (pre (semantics (Spec
     (Predicate
        (fun s : S data =>
         {t0 : S data &
         (prod {t1 : S data &
          prod (prod {f : nat -> nat & pa_model t1 ptr f} (find t1 ptr = Some vInPtr))
          (prod (forall (p' : M.key) (x : data), find t1 p' = Some x -> p' <> t)
           (t0 = update t1 t vInPtr))} 
          (prod (forall (p' : M.key) (x : data), find t0 p' = Some x -> p' <> done)
           (s = update t0 done (ResultGet None))))%type})
        (fun (s : S data)
           pres
           (v : nat) (s' : S data) =>
         (let (f, _) := fst (fst (projT2 (fst (projT2 pres)))) in
          fun (v0 : nat) (_ : S data) => v0 = f i) v s')))))

                     (pre (semantics (Spec (BindPT
          (Predicate (fun s : S data => Inv ptr t done i s)
             (fun (ss : S data) (_ : Inv ptr t done i ss) 
                (_ : unit) (s : S data) => Inv ptr t done i s))
          (fun _ : unit =>
           Predicate (fun s : S data => Inv ptr t done i s)
             (fun (ss : S data) (pres : Inv ptr t done i ss) 
                  (v : nat) (_ : S data) => projT1 pres i = v))))))).  *)
  refine_simpl.
  unfold Inv.
  exists s1.
  repeat split; auto.
  apply pa_model_sep_padata.
  unfold not; intros H; inversion H; symmetry in H1; apply n in H1; now apply H1.
  apply pa_model_copy with (p := ptr); auto.
  assert (Ha : pa_model s0 ptr s1); auto.
  apply pa_model_dist in X0.
  destruct X0.
  exists x.
  split. apply dist_sepT.
  apply dist_sepT; auto.

  

    unfold not; intros.
    clear e1 Ha.
    induction d; subst. 
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.

    unfold not; intros.
    clear e1 Ha.
    induction d; subst.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    inversion H1.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    auto.
    
    unfold not; intros.
    clear e1 Ha.
    induction d; subst.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.    
  
  exists s1.
  split; auto.
  apply pa_model_sep_padata.
  unfold not; intros H; inversion H; symmetry in H1; apply n in H1; now apply H1.
  apply pa_model_sep'; auto.
  destruct (find_eqdec s0 t); auto.
  destruct e; apply n0 in H; exfalso; auto.
  intros; auto.
  now destruct X.

  Focus 3.
  refine_simpl. unfold Inv in i0.
  destruct i0; simpl in *.
  destruct_conjs.
  assert (Ha : pa_model (update (update s1 t vInPtr) done (ResultGet None)) ptr s2).
  apply pa_model_sep'.
  admit.
  apply pa_model_sep'; auto.
  admit. (* InT ... x0 -> False *)
  assert (Ha1 := Ha).
  apply pa_model_dist in Ha.
  destruct Ha.
  pose (pa_model_dist_eq Ha1 d0 _ (f _ d0)).
  assert (Ha : s2 = s4).
  eapply pa_model_fun. apply p1. auto.
  now subst.

  eapply whileSpec'.
  admit.
  refine_simpl. apply X.
  refine_simpl. auto.
  unfold Inv in *; destruct_conjs.
  intros.

  apply whileSpec; unfold Inv in *.
  - refine_simpl; exists X; repeat split; eauto.
  - READ t vInT. inversion p; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    destruct s2; eauto.
    RETURN tt.
    admit. admit.
    RETURN tt; inversion p; rewrite H in e; inversion e.
    RETURN tt; inversion p0; rewrite H in e; inversion e.
  - RETURN tt.
    exists s1; repeat split; eauto.
    intros.
    admit.
  - unfold Inv; READ done vInDone.
    destruct s1; eauto.
    destruct vInDone.
    RETURN 0.
    destruct s2; rewrite e in e1; inversion e1.
    RETURN 0.
    destruct s2; rewrite e in e1; inversion e1.
    destruct o.
    RETURN n.
    destruct s2; rewrite e in e1; inversion e1.
    reflexivity.
    RETURN 0.
    destruct s2; rewrite e in e1; inversion e1.
    admit. (* missing Is_false (cond) when splitting the proof before *)
    RETURN 0.
    destruct s2; rewrite e in e1; inversion e1.    
Admitted.  


  
(* get (using a loop) refinement *)
Lemma getRefinementNewInvUgly :  forall ptr i, wrefines (getSpec ptr i) (getNewInvUgly ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  apply newSpec'; intro t.
  apply newSpec'; intro done.
  apply whileSpec.
  - refine_simpl.
    exists s1; repeat split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H;
    symmetry in H1; apply n in H1; now apply H1.
    eapply pa_model_copy; eauto.
    apply pa_model_dist in X0; destruct X0.
    exists x.
    split.
    eapply dist_sepT.
    eapply dist_sepT.
    auto.

    unfold not; intros.
    clear e1.
    induction d; subst. 
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.

    unfold not; intros.
    clear e1.
    induction d; subst.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    inversion H1.
    inversion H; subst.
    rewrite <- findNUpdate with (p' := t) (v := vInPtr) in e.
    apply n in e; now apply e.
    unfold not; intros; subst.
    apply n0 in e; now apply e.
    auto.
    
    unfold not; intros.
    clear e1.
    induction d; subst.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion H1.
    inversion H; subst.
    apply n0 in e. now apply e.
    inversion d; subst; eauto.    
    
    exists s1.
    split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H;
    symmetry in H1; apply n in H1; now apply H1.
    apply pa_model_sep'; auto.
    destruct (find_eqdec s0 t); auto.
    destruct e; apply n0 in H; exfalso; auto.
  - READ t vInT.
    inversion p; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    destruct s2; eauto.
    RETURN tt; eauto.
    eexists; repeat split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros HInv.
    destruct s2; rewrite e in HInv; inversion HInv.
    eauto.
    exists s1.
    split; auto.
    apply dist_sepT; auto.

    clear p0.
    unfold not; intros.
    induction d; subst.
    inversion H; subst.
    destruct s2; rewrite e2 in e; inversion e.
    inversion H1.
    inversion H; subst.
    destruct s2; rewrite e2 in e; inversion e.
    auto.
        
    exists s3; eauto.
    split; auto.
    inversion p; subst; rewrite e0 in H; inversion H; subst.
    apply pa_model_sep_padata.
    unfold not; intros HInv; destruct s2; rewrite e in HInv; inversion HInv.
    auto.
    inversion p; subst; rewrite e0 in H; inversion H; now subst.    
    destruct (Nat.eq_dec i n).
    subst.
    rewrite PeanoNat.Nat.eqb_refl.
    WRITE done (ResultGet (Some n0)).
    destruct s2; eauto.
    RETURN tt; eauto.
    eexists; split; eauto. 
    apply pa_model_sep_padata; eauto.
    unfold not; intros HInv.
    destruct s2; auto; rewrite e in HInv; inversion HInv.
    destruct s2; rewrite e in i.
    exfalso; auto; simpl in i.
    split.
    exists s1.
    split.
    apply dist_sepT; auto.

    clear p0 p1.
    unfold not; intros.
    induction d; subst.
    inversion H; subst.
    rewrite e in e2; inversion e2.
    inversion H1.
    inversion H; subst.
    rewrite e in e2; inversion e2.
    apply IHd.
    intros; apply f; auto.
    auto.

    auto.
    split.
    left; rewrite findUpdate; repeat apply f_equal.
    inversion p0; rewrite H in e0; inversion e0; subst.
    unfold upd; now rewrite <- beq_nat_refl.
    exists s3; split; auto.
    apply pa_model_sep_padata; auto.
    rewrite e; unfold not; intros HInv; inversion HInv.
    apply Nat.eqb_neq in n1.
    rewrite n1.
    READ p vInT'.
    inversion p0; subst; rewrite e in H; inversion H; subst.
    inversion X; subst; eauto.
    WRITE t vInT'.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e1 in H; inversion H; subst; clear H.
    exists f0.
    repeat split.

    eapply pa_model_desc; eauto.
    
    exists s1.
    split; auto; apply dist_sepT; auto.
    destruct s2; auto.
    left. rewrite findNUpdate; eauto 1. rewrite e. repeat apply f_equal. unfold upd; now rewrite n1.
    unfold not; intros; subst; rewrite e1 in e; inversion e.
    right; rewrite findNUpdate; eauto 1; unfold not; intros; subst; rewrite e1 in e; inversion e.
    exists s3. split; auto.
    assert (Ha : pa_model pre ptr s3) by assumption.
    apply pa_model_dist in Ha; destruct Ha.
    eapply pa_model_sep_uglyT; eauto.
    assert (Ha : x = s1) by (eapply dist_fun; eauto). subst.
    auto.
    rewrite <- e2.
    unfold upd; now rewrite n1.
    RETURN tt; eauto.
    inversion p; subst; rewrite e in H; inversion H.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e in H; inversion H.
  - READ done vInDone.
    destruct s3; eauto.
    destruct vInDone.
    admit.
    admit.
    destruct o.
    RETURN n.
    destruct s3.
    rewrite e1 in e.
    inversion e.
    subst.
Admitted.



(* ENDS HERE: new get *)



Definition getNewInv (ptr : Ptr) (i : nat) : WhileL data nat. 
refine (
  Read ptr (fun vInPtr =>
  New vInPtr (fun t =>
  New (ResultGet None) (fun done =>
  While (fun s => { f : nat -> nat & (prod (pa_model s t f) (prod
                                (sum (find s done = Some (ResultGet (Some (f i))))
                                     (find s done = Some (ResultGet None)))
                                ({ f' : nat -> nat & (prod (pa_model s ptr f')
                                                       (f i = f' i))})))})
        (fun s => negb (data_get_eqb_some (find s done)))
        (Read t (fun vInT => _ )) (* the body is refined below *)
        (Read done (fun vInDone =>
         match vInDone with
           | ResultGet (Some a) => Return _ a
           | _ => Return _ 0 (* absurd *)
         end)))))).
(* body of the loop *)
destruct vInT as [ f | j v t' | | ].
refine (Write done (ResultGet (Some (f i))) (Return _ tt)).
refine (if Nat.eqb i j
        then _
        else _).
refine (Write done (ResultGet (Some v)) (Return _ tt)).
refine (Read t' (fun vInT' => Write t vInT' (Return _ tt))).
refine (Return _ tt). (* absurd: t will never point to a result *)
refine (Return _ tt). (* absurd: t will never point to a result *)
Defined.
  
(* get (using a loop) refinement *)
Lemma getRefinementNewInv :  forall ptr i, wrefines (getSpec ptr i) (getNewInv ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  apply newSpec'; intro t.
  apply newSpec'; intro done.
  apply whileSpec.
  - refine_simpl.
    exists s1; repeat split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H;
    symmetry in H1; apply n in H1; now apply H1.
    eapply pa_model_copy; eauto.
    exists s1.
    split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros H; inversion H;
    symmetry in H1; apply n in H1; now apply H1.
    apply pa_model_sep'; auto.
    destruct (find_eqdec s0 t); auto.
    destruct e; apply n0 in H; exfalso; auto.
  - READ t vInT.
    inversion p; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    destruct s1; eauto.
    RETURN tt; eauto.
    eexists; repeat split; eauto.
    apply pa_model_sep_padata.
    unfold not; intros HInv.
    destruct s1; rewrite e in HInv; inversion HInv.
    eauto.
    exists s2; eauto.
    split; auto.
    inversion p; subst; rewrite e0 in H; inversion H; subst.
    apply pa_model_sep_padata.
    unfold not; intros HInv; destruct s1; rewrite e in HInv; inversion HInv.
    auto.
    inversion p; subst; rewrite e0 in H; inversion H; now subst.    
    destruct (Nat.eq_dec i n).
    subst.
    rewrite PeanoNat.Nat.eqb_refl.
    WRITE done (ResultGet (Some n0)).
    destruct s1; eauto.
    RETURN tt; eauto.
    eexists; split; eauto. 
    apply pa_model_sep_padata; eauto.
    unfold not; intros HInv.
    destruct s1; auto; rewrite e in HInv; inversion HInv.
    destruct s1; rewrite e in i.
    exfalso; auto; simpl in i.
    split. left; rewrite findUpdate; repeat apply f_equal.
    inversion p0; rewrite H in e0; inversion e0; subst.
    unfold upd; now rewrite <- beq_nat_refl.
    exists s2; split; auto.
    apply pa_model_sep_padata; auto.
    rewrite e; unfold not; intros HInv; inversion HInv.
    apply Nat.eqb_neq in n1.
    rewrite n1.
    READ p vInT'.
    inversion p0; subst; rewrite e in H; inversion H; subst.
    inversion X; subst; eauto.
    WRITE t vInT'.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e1 in H; inversion H; subst; clear H.
    exists f.
    repeat split.
    admit. (* apparently provable by e0 and e1 *)
    destruct s1; auto.
    left. rewrite findNUpdate; auto. rewrite e. repeat apply f_equal. unfold upd; now rewrite n1.
    unfold not; intros; subst. rewrite e1 in e; inversion e.
    right; auto; rewrite findNUpdate; eauto 1;
    unfold not; intros; subst; rewrite e1 in e; inversion e.
    exists s2. split; auto.
    admit. (* how to prove this? *)
    unfold upd in e2; now rewrite n1 in e2.
    RETURN tt; eauto.
    inversion p; subst; rewrite e in H; inversion H.
    RETURN tt; eauto.
    inversion p0; subst; rewrite e in H; inversion H.
  - READ done vInDone.
    destruct s2; eauto.
    destruct vInDone.
    admit.
    admit.
    destruct o.
    RETURN n.
    destruct s3.
    rewrite e1 in e.
    inversion e.
    subst.
    Print pa_model.
    
    rewrite e0 in i0; simpl in i0; exfalso; auto.
    admit.

    
Admitted.



(* get (using a loop) refinement *)
Lemma getRefinement :  forall ptr i, wrefines (getSpec ptr i) (get ptr i).
Proof.
  intros.
  unfold get, getSpec.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  apply newSpec'; intro t.
  apply newSpec'; intro done.


  apply whileSpec.
  - refine_simpl.
    inversion X0; subst.
    rewrite e1 in H; inversion H; subst; clear H.
    eexists.
    apply pa_model_array.
    rewrite findNUpdate.
    rewrite findUpdate.
    reflexivity.
    apply n with (x := (Arr s1)).
    now rewrite findUpdate.
    rewrite e1 in H; inversion H; subst; clear H.
    eexists.
    eapply pa_model_diff.
    rewrite findNUpdate.
    rewrite findUpdate.
    reflexivity.
    eapply n.
    now rewrite findUpdate.
    apply pa_model_sep'.
    destruct (find_eqdec (update s0 t (Diff i0 v p')) done); auto.
    destruct e; exfalso; eapply n; eauto.
    apply pa_model_sep'.
    destruct (find_eqdec s0 t); auto.
    destruct e; exfalso; eapply n0; eauto.
    apply X.
    eapply n; now rewrite findUpdate.
    eauto.
  - READ t vInT.
    inversion X0; subst; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    RETURN tt; eauto.
    destruct (Nat.eq_dec i n).
    subst.
    rewrite PeanoNat.Nat.eqb_refl.
    WRITE done (ResultGet (Some n0)).
    RETURN tt; eauto.
    inversion X0; subst; rewrite e0 in H; inversion H; subst; clear H.
    exists (upd f i0 v).
    apply pa_model_diff with (p' := p').
    rewrite findNUpdate. apply e0. auto.
    apply pa_model_sep_padata; auto.
    unfold not; intros H; rewrite X in H; inversion H.
    apply Nat.eqb_neq in n1.
    rewrite n1.
    READ p vInT'.
    inversion X0; subst; rewrite e in H; inversion H; subst; clear H.
    inversion X1; eauto.
    WRITE t vInT'.
    RETURN tt; eauto.
    inversion X0; subst; rewrite e1 in H; inversion H; subst; clear H.
    inversion X1; subst; rewrite e0 in H; inversion H; subst; clear H.
    eauto.
    exists (upd f0 i2 v0).
    eapply pa_model_diff.
    now rewrite findUpdate.
    admit. (* seems to follow from X2, if t <> p'0 *)
    RETURN tt; eauto.
    RETURN tt; eauto.
  - READ done vInDone.
    destruct vInDone.
    Focus 3.
    destruct o.
    RETURN n.
    rewrite X in e; inversion e; subst; clear e.
    admit.
    Set Ltac Debug.
    RETURN 0.
    rewrite X in i0; inversion i0.
    RETURN 0.
    rewrite X in i0; inversion i0.
    RETURN 0.
    rewrite X in i0; inversion i0.
    RETURN 0.
    rewrite X in i0; inversion i0.
Admitted.

(* A (non-executable) implementation fulfilling only partial-correctness,
   using a recursive approach *)

Definition get' (ptr : Ptr) (i : nat) : WhileL data nat := 
  Read ptr
       (fun ptrVal => match ptrVal with
                       | Arr f => Return _ (f i)
                       | Diff j v ptr' =>
                         if beq_nat i j
                         then Return _ v
                         else getSpec ptr' i
                       | _ => Return _ 0 (* absurd *)
                     end).

Lemma getRefinement' : forall ptr i, getSpec ptr i ⊑ get' ptr i.
Proof.
  intros.
  READ ptr vInPtr.
  inversion X0; subst; simpl in *; eauto.
  destruct vInPtr as [ | j v ptr' | | ]; simpl.
  (* Original persistent array *)
  - apply returnStep; unfold_refinements; refine_simpl.
    inversion X; subst; auto.
    rewrite e in H; inversion H; now subst.
    rewrite e in H; inversion H.
  (* Single modification of other persistent array *)
  - destruct (eq_nat_dec i j).
    + subst.
      rewrite <- beq_nat_refl.
      apply returnStep; unfold_refinements; refine_simpl.
      inversion X.
      subst; simpl in *.
      rewrite e in H; inversion H.
      subst; simpl in *.
      unfold upd.
      rewrite H in e; inversion e; subst.
      subst; now rewrite <- beq_nat_refl.
    + rewrite <- PeanoNat.Nat.eqb_neq in n.
      rewrite n; unfold getSpec, wrefines; simpl.
      eapply (Refinement _ _ _).
      Unshelve. Focus 2.
      unfold subset; simpl. 
      intros s [[f H1] H2].
      inversion H1; rewrite H in H2; inversion H2.
      subst; clear H2.
      now exists f0.
      refine_simpl.
      inversion X0; rewrite e in H; inversion H.
      subst; clear H.
      unfold upd; rewrite n.
      destruct X0. admit.
      assert (Ha : find s p = Some (Diff i1 v p'0)). apply e0.
      rewrite e in Ha; inversion Ha; subst; clear Ha; simpl in *.
      admit. (* looks like we could prove this using X... *)
  - RETURN 0; inversion X; rewrite e in H; inversion H.
  - RETURN 0; inversion X; rewrite e in H; inversion H.
Admitted.

(* attempt at defining recursion *)
Inductive WhileL' (I : Type) (O : I -> Type) (a : Type) : Type :=
  | New'    : forall v, v -> (Ptr -> WhileL' O a) -> WhileL' O a
  | Read'   : forall v, Ptr -> (v -> WhileL' O a) -> WhileL' O a
  | Write'  : forall v, Ptr -> v -> WhileL' O a  -> WhileL' O a
  | Spec'   : PT a -> WhileL' O a
  | Call    : forall (i : I), (O i -> WhileL' O a) -> WhileL' O a
  | Return' : a -> WhileL' O a.

(** STOP HERE **)

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



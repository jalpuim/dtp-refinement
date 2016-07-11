Require Import Arith.
Require Export FMapAVL.
Require Import FSets.FMapFacts.
Require Export Coq.Structures.OrderedType.
Require Import Omega.
Require Import String.

(* Addresses *)

Module Addr <: OrderedType.

  Inductive addr : Type :=
    MkAddr : nat -> addr.

  Definition fromAddr (p : addr) : nat :=
    match p with
      | MkAddr x => x
    end.

  Definition t := addr.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec (p p' : addr) : {eq p p'} + {~ eq p p'}. 
    unfold eq; repeat decide equality.
  Defined.

  Definition lt (p p' : addr) := lt (fromAddr p) (fromAddr p').

  Ltac destruct_addrs := unfold lt in *; unfold eq in *; repeat match goal with
                                 | [H : addr |- _ ] => destruct H
                               end; simpl fromAddr in *.
  
  Definition lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
    intros; destruct_addrs; now eauto with arith.
  Qed.

  Definition lt_not_eq : forall x y, lt x y -> ~ eq x y.
    intros; destruct_addrs; intros F; inversion F; omega.
  Qed.
  Definition compare p p' : Compare lt eq p p'.
    destruct p as [x]; destruct p' as [y].
    remember (nat_compare x y) as c; destruct c.
    - apply EQ; assert (x = y) by now (apply nat_compare_eq).
      now subst. 
    - apply LT; assert (x < y) by now (apply nat_compare_lt).
      now trivial.
    - apply GT; assert (x > y) by now (apply nat_compare_gt).
      now trivial.
  Defined.

  Definition incr (addr : Addr.t) : Addr.t :=
    match addr with
      | MkAddr n => MkAddr (S n)
    end.

  Definition max (addr addr' : Addr.t) : Addr.t :=
    match compare addr addr' with
        | GT _ => addr
        | _ => addr'
    end.

  Lemma maxProp1 : forall n m, Addr.fromAddr n <= Addr.fromAddr (Addr.max n m).
    Proof.
      intros n m; unfold Addr.max.
      destruct (Addr.compare n m); unfold Addr.lt in *; unfold Addr.eq in *; subst; omega.
    Qed.  

  Lemma maxProp2 : forall n m, Addr.fromAddr m <= Addr.fromAddr (Addr.max n m).
    Proof.
      intros n m; unfold Addr.max.
      destruct (Addr.compare n m); unfold Addr.lt in *; unfold Addr.eq in *; subst; omega.
    Qed.

  Hint Resolve maxProp1 maxProp2.

  Open Local Scope string_scope.

  Definition printAddr (a : addr) (show : nat -> string) : string := 
    "x" ++ show (fromAddr a).

End Addr.

(** Heaps **)

Module M := FMapAVL.Make(Addr).
Module MFacts := WFacts_fun(Addr)(M).
Import MFacts.

Section Heaps.
  Variable (a : Type). 
  Definition heap: Type :=  M.t a.

  Definition find (h: heap) k := M.find k h.

  Definition update (h : heap) k v := M.add k v h.

  Definition empty : heap := M.empty a.

  (** Lemmas **)
  Lemma findUpdate (h : heap) (p : Addr.t) (d : a) :
    find (update h p d) p = Some d.
  Proof. 
    apply M.find_1; now apply M.add_1.
  Qed.

  Lemma findNUpdate1 (h : heap) (p p' : Addr.t) (D : p <> p') (x : option a) (v : a) :
    find h p = x ->
    find (update h p' v) p = x.
  Proof.
    intros H; unfold find, update; rewrite add_neq_o; now eauto.
  Qed.

  Lemma findNUpdate2 (h : heap) (p p' : Addr.t) (D : p <> p') (x : option a) (v : a) :
    find h p = x ->
    x = find (update h p' v) p.
  Proof.
    intros H; unfold find, update; rewrite add_neq_o; now eauto.
  Qed.

  Hint Resolve findUpdate findNUpdate1 findNUpdate2.

  Lemma findIn : forall ptr s v,
    find s ptr = Some (v) ->
    M.In (elt:=a) ptr s.
  Proof.
    unfold find; intros.
    apply MFacts.in_find_iff.
    unfold not; intros; auto.
    rewrite H0 in H; inversion H.
  Qed.

  (** Allocation **)

  Fixpoint maxTree {e : Type} (t : M.Raw.tree e) (a : Addr.t) : Addr.t :=
    match t with
      | M.Raw.Leaf _ => Addr.incr a
      | M.Raw.Node l y e r h => maxTree r (Addr.max a y)
    end.

  Definition maxHeap (h : heap) (x : Addr.t) : Addr.t.
    destruct h. apply (maxTree this x).
  Defined.

  (*
  Definition maxHeap (h : heap) (a : Addr.t) :=
    match h with
     | {| M.this := t|} => maxTree t a
    end.
  *)

  Definition alloc (h : heap) : Addr.t := maxHeap h (Addr.MkAddr 0).

  (* Properties of allocate *)

  Lemma maxStep {e : Type} (t : heap) : forall p, Addr.lt p (maxTree (M.this t) p).
    Proof.
      destruct t as [this H]; induction this.
      - destruct p; unfold Addr.lt; simpl; omega.
      - simpl; intros p; inversion H; subst.
        unfold Addr.lt; eapply le_lt_trans; [now (apply Addr.maxProp1) | now (apply (IHthis2 H6))].
    Qed.

  Lemma isLeast (t : heap) : forall p, M.Raw.lt_tree (maxHeap t p) (M.this t).
    destruct t as [this is_bst]; induction this.
    - intros; now apply M.Raw.Proofs.lt_leaf.
    - inversion is_bst; subst; simpl in *; intros p. 
      assert (ltM1 : Addr.fromAddr k <= Addr.fromAddr (Addr.max p k)) by apply (Addr.maxProp2 p k).
      assert (ltM2 : Addr.fromAddr (Addr.max p k) < Addr.fromAddr (maxTree this2 (Addr.max p k)))
          by apply (maxStep (e:=a) {| M.this := this2; M.is_bst := H5 |}).
      assert (ltM3 : Addr.fromAddr k < Addr.fromAddr (maxTree this2 (Addr.max p k))) by omega.
      apply M.Raw.Proofs.lt_tree_node.
      * apply (M.Raw.Proofs.lt_tree_trans ltM3 H6).
      * now apply IHthis2.
      * assumption. 
    Qed.
      
  Lemma allocNotIn (h : heap) : ~ M.In (alloc h) h.
    assert (H : ~ M.Raw.In (alloc h) (M.this h)) by apply M.Raw.Proofs.lt_tree_not_in, isLeast.
    now (intros F; apply H; apply M.Raw.Proofs.In_alt).
  Qed.

  Lemma allocFresh (h : heap) : find h (alloc h) = None.
  Admitted.


  Lemma findAlloc1 (h : heap) (v : a) (p : Addr.t) :
    M.In p h ->
    find (update h (alloc h) v) p = find h p.
  Proof.
    intro HIn; unfold find; apply add_neq_o.
    unfold not; intros; subst; now apply allocNotIn in HIn.
  Qed.

  Lemma findAlloc2 (h : heap) (v : a) (p : Addr.t) :
    M.In p h ->
    find h p = find (update h (alloc h) v) p.
  Proof.
    intro HIn; unfold find; symmetry.
    now apply findAlloc1.
  Qed.

  Hint Resolve allocFresh findAlloc1 findAlloc2.

  Lemma allocDiff1 (v : a) (h : heap) (ptr : Addr.t) :
    find h ptr = Some v -> 
    ptr <> alloc h.
  Admitted.

  Lemma allocDiff2 (v : a) (h : heap) (ptr : Addr.t) :
    find h ptr = Some v -> 
    alloc h <> ptr.
  Admitted.

  Lemma someIn (v : a) (h : heap) (ptr : Addr.t) :
    find h ptr = Some v -> M.In ptr h.
  Admitted.

  Lemma heapGrows {b: Type} (s : heap) (x y : a) (ptr : Addr.t) :
    find s ptr = Some (x) ->
    {z : a | find (update s (alloc s) (x)) ptr = Some (x)}.
    Proof.
      intros; exists x; eapply findNUpdate1; try eapply allocDiff1; eassumption.
    Qed.

  Lemma someExists (s : heap) (ptr : Addr.t) (x : a) :
    find s ptr = Some x -> {v : a | find s ptr = Some x}.
    Proof.
      intros; now exists x.
    Qed.

  Lemma someExistsT (s : heap) (ptr : Addr.t) (x : a) :
    find s ptr = Some x -> {v : a & find s ptr = Some x}.
    Proof.
      intros; now exists x.
    Qed.


  Lemma freshDiff1 (s : heap) (p q : Addr.t) (v : a) :
    (forall p' : M.key, M.In  p' s -> p' <> p) ->
    find s q = Some v ->
    p <> q.
    Proof.
      intros H1 H2 Eq;
      now (apply (H1 q); [eapply (someIn _ _ _ H2) | symmetry]).
    Qed.

  Lemma freshDiff2 (s : heap) (p q : Addr.t) (v : a) :
    (forall p' : M.key, M.In  p' s -> p' <> p) ->
    find s q = Some v ->
    q <> p.
    Proof.
      intros H1 H2 Eq;
      now (apply (H1 q); [eapply (someIn _ _ _ H2) | ]).
    Qed.    



  Hint Resolve allocDiff1 allocDiff2 heapGrows someExists someExistsT someIn findAlloc1 findAlloc2 freshDiff1 freshDiff2 not_eq_sym.
End Heaps.
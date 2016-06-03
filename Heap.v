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

Inductive Dynamic : Type :=
  | dyn : forall a, a -> Dynamic.

Definition heap: Type := M.t Dynamic.

Definition find (h: heap) k := M.find k h.

Definition update (h : heap) k v := M.add k v h.

Definition empty : heap := M.empty Dynamic.

Lemma read (a : Type) (h : heap) (k : Addr.t) : (exists v, M.MapsTo k (dyn a v) h) -> a.
Admitted.


(** Allocation **)

Fixpoint maxTree {e : Type} (t : M.Raw.tree e) (a : Addr.t) : Addr.t :=
  match t with
    | M.Raw.Leaf _ => Addr.incr a
    | M.Raw.Node l y e r h => maxTree r (Addr.max a y)
  end.

Definition maxHeap (h : heap) (a : Addr.t) : Addr.t.
  destruct h. apply (maxTree this a).
Defined.

(*
Definition maxHeap (h : heap) (a : Addr.t) :=
  match h with
   | {| M.this := t|} => maxTree t a
  end.
*)

Definition alloc (h : heap) : Addr.t := maxHeap h (Addr.MkAddr 0).

(* Properties of allocate *)

Lemma maxStep {e : Type} (t : heap) : forall a, Addr.lt a (maxTree (M.this t) a).
  Proof.
    destruct t as [this H]; induction this.
    - destruct a; unfold Addr.lt; simpl; omega.
    - simpl; intros a; inversion H; subst.
      unfold Addr.lt; eapply le_lt_trans; [now (apply Addr.maxProp1) | now (apply (IHthis2 H6))].
  Qed.

Lemma isLeast (t : heap) : forall a, M.Raw.lt_tree (maxHeap t a) (M.this t).
  destruct t as [this is_bst]; induction this.
  - intros; now apply M.Raw.Proofs.lt_leaf.
  - inversion is_bst; subst; simpl in *; intros a. 
    assert (ltM1 : Addr.fromAddr k <= Addr.fromAddr (Addr.max a k)) by apply (Addr.maxProp2 a k).
    assert (ltM2 : Addr.fromAddr (Addr.max a k) < Addr.fromAddr (maxTree this2 (Addr.max a k)))
        by apply (maxStep (e:=Dynamic) {| M.this := this2; M.is_bst := H5 |}).
    assert (ltM3 : Addr.fromAddr k < Addr.fromAddr (maxTree this2 (Addr.max a k))) by omega.
    apply M.Raw.Proofs.lt_tree_node.
    * apply (M.Raw.Proofs.lt_tree_trans ltM3 H6).
    * now apply IHthis2.
    * assumption. 
  Qed.
    
Lemma allocFresh (h : heap) : ~ M.In (alloc h) h.
  assert (H : ~ M.Raw.In (alloc h) (M.this h)) by apply M.Raw.Proofs.lt_tree_not_in, isLeast.
  now (intros F; apply H; apply M.Raw.Proofs.In_alt).
Qed.


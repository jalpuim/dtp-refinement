

Set Implicit Arguments.

(** Basic Heap model **)
Variable ptr : Set.
Variable ptr_eq_dec : forall (a b : ptr), {a = b} + {a <> b}.

Inductive dynamic : Type :=
  | Dyn : forall T, T -> dynamic.

Definition heap := ptr -> option dynamic.

(** Simple heap creation and manipulation functions **)

Definition empty : heap := fun _ => None.

Definition singleton (p : ptr) (v : dynamic) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else None.

Definition read (h : heap) (p : ptr) : option dynamic := h p.

Definition write (h : heap) (p : ptr) (v : dynamic) : heap :=
  fun p' => if ptr_eq_dec p' p then Some v else h p'.

Definition free (h : heap) (p : ptr) : heap :=
  fun p' => if ptr_eq_dec p' p then None else h p'.

Infix "|-->" := singleton (at level 35, no associativity) : heap_scope.
Notation "a # b" := (read a b) (at level 55, no associativity) : heap_scope.
Notation "h ## p <- v" := (write h p v) (no associativity, at level 60, p at next level) : heap_scope.
Infix "###" := free (no associativity, at level 60) : heap_scope.

(** Properties of heaps **)

Definition hprop := heap -> Prop.

Definition hprop_empty : hprop := eq empty.
Notation "'__'" := hprop_empty : hprop_scope.
Notation "'emp'" := hprop_empty : hprop_scope.

Definition hprop_any : hprop := fun _ => True.
Notation "??" := hprop_any : hprop_scope.

Open Local Scope heap_scope.

Definition hprop_and (p1 p2 : hprop) : hprop := fun h => p1 h /\ p2 h.
Infix "&" := hprop_and (at level 39, left associativity) : hprop_scope.

Definition hprop_ex T (p : T -> hprop) : hprop := fun h => exists v, p v h.
Notation "'Exists' v :@ T , p" := (hprop_ex (fun v : T => p)) 
  (at level 90, T at next level).

Definition ptsto_any(p:ptr) : hprop := Exists A :@ Set, Exists v :@ A, fun h => (h#p = Some (Dyn v)).
Notation "p '-->?'" := (ptsto_any p 0) (at level 38, no associativity) : hprop_scope.
Notation "p '-[' q ']->?'" := (ptsto_any p q) (at level 38, no associativity) : hprop_scope.


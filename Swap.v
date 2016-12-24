

Require Import While.
Require Import Refinement.
Require Import Heap.
(************************************************************

                             SWAP EXAMPLE

*************************************************************)

(** Just a brief example showing how the language currently looks like 
    Contains some testing definitions to be moved elsewhere once proven.
**)
Definition SWAP {a : Type} (p q : Ptr): WhileL a unit := 
  Spec (Predicate
          (fun s => prod {x : a | find s p = Some x} {y : a | find s q = Some y})
          (fun s _ _ s' => find s p = find s' q /\ find s q = find s' p)).

Definition swapResult {a : Type} (P : Ptr) (Q : Ptr) (D : P <> Q) :
  {c : WhileL a unit & SWAP P Q ⊑ c}.
Proof.
  econstructor; unfold SWAP.
  READ Q x.
  NEW x T.
  READ P y. 
  WRITE Q y. 
  READ T z. 
  WRITE P z. 
  RETURN tt.
  assert (T <> Q) by eauto.
  assert (P <> T) by eauto.
  context_simpl; context_clean.
  now simpl_lookup.
  assert (T <> Q) by eauto.
  assert (P <> T) by eauto.
  context_simpl; context_clean.
  now simpl_lookup.
Qed.  
  

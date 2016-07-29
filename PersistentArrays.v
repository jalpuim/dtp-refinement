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

(* Tactics copied from While Section. To be removed later. *)


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
    apply someIn in e0; apply pa_model_sep; auto.
    (* TODO Maybe change pa_model_sep to use find instead of M.In? *)
    unfold not; intros H. eapply n with (p' := res); auto.
    admit.
    apply someIn in e0; apply pa_model_sep; auto.
    unfold not; intros H. eapply n with (p' := res); auto.
    admit.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
  - RETURN ptr.
    inversion X; subst; rewrite H in e; inversion e.
Admitted.

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
  While (fun s => prod ({ f : nat -> nat & pa_model s t f })
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

Lemma refineSkipPT :
  forall (w1 w2 : PT data unit),
    Refines w1 w2 -> 
    Refines w1 (SeqPT w2 (Predicate (fun _ => True)
                                    (fun s _ v s' => s = s' /\ v = tt))).
Proof.
  intros.
  destruct X.
  destruct w1, w2.
  refine_simpl.
  eapply (Refinement _ _ _).
  Unshelve. Focus 2.
  refine_simpl; eauto.
  refine_simpl.
  assert (Ha : X0 = tt) by now induction X0.
  subst.
  Unshelve. Focus 2.
  apply d.
  apply X.
  apply s.
  apply X1.
Qed.  


(* get (using a loop) refinement *)
Lemma getRefinement :  forall ptr i, wrefines (getSpec ptr i) (get ptr i).
Proof.
  intros.
  unfold get.
  READ ptr vInPtr.
  inversion X0; subst; eauto.
  NEW vInPtr t.
  (* NEW (ResultGet None) done. *)
  apply newSpec; [ | intros done]; simpl; intros. (* ; goal_simpl. *)
  destruct_conjs.
  exists (update s (alloc s) (ResultGet None)).
  subst. repeat split.
  exists s0.
  admit.
  rewrite findNUpdate.
  rewrite findNUpdate.
  auto.
  eapply n.
  eassumption.
  admit. (* heap lemma? *)
  intros.
  eapply n.
  admit. (* heap lemma? *)
  admit. (* heap lemma? *)
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
    admit. (* do we need to re-formulate newSpec? *)
    apply pa_model_sep'.
    admit. (* do we need to re-formulate newSpec? *)
    apply X.
    eapply n; now rewrite findUpdate.
    eauto.
  - READ t vInT.
    inversion X0; subst; eauto.
    destruct vInT.
    WRITE done (ResultGet (Some (n i))).
    RETURN tt.
    destruct (Nat.eq_dec i n).
    subst.
    rewrite PeanoNat.Nat.eqb_refl.
    WRITE done (ResultGet (Some n0)).
    RETURN tt.
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
    RETURN tt.
    inversion X0; subst; rewrite e1 in H; inversion H; subst; clear H.
    inversion X1; subst; rewrite e0 in H; inversion H; subst; clear H.
    eauto.
    exists (upd f0 i2 v0).
    eapply pa_model_diff.
    now rewrite findUpdate.
    admit. (* seems to follow from X2, if t <> p'0 *)
    RETURN tt.
    RETURN tt.
  - READ done vInDone.
    destruct vInDone.
    RETURN 0.
    rewrite X in i0; inversion i0.
    RETURN 0.
    rewrite X in i0; inversion i0.
    destruct o.
    RETURN n.
    admit.
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



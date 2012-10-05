(* TODO: 
  - How to deal with allocation of vars? 
    Maybe its better to handle this from the outset
  - Total vs partial correctness. Should we worry about the 
    variant of a while?
  - How to handle frame rules? What can change and what cannot?
*)

Require Import Bool.

Module Refinement.

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

Notation "PT1 ⊑ PT2" := (Refines PT1 PT2) (at level 90) : type_scope.

Notation "[ p , q ]" := (Predicate p q) (at level 70) : type_scope.

Ltac refine_simpl := unfold subset, pre, post, extend; simpl; auto.

(*** Guarded command language ***)

(*** Structural laws ***)

Lemma strengthenPost (P : Pow S) (Q1 Q2 : forall s, P s -> Pow S) :
  (forall (s : S) (p : P s), Q1 s p ⊂ Q2 s p) -> 
  [ P , Q2 ] ⊑ [ P , Q1 ].
Proof.
  intros.
  set (d := fun (s : S) (H: P s) => H).
  apply (Refinement ([P, Q2]) ([P, Q1]) d).
  intros. unfold post. unfold pre in x. unfold subset in *. intros. apply H.
  simpl in *; assumption.
Qed.

Lemma weakenPre (P1 P2 : Pow S) (Q : forall s, P2 s -> Pow S) (f : P1 ⊂ P2) :
  [ P1 , (fun s p s' => Q s (f s p) s') ] ⊑ [ P2 , Q ].
Proof.
  intros.
  apply (Refinement ([P1, fun (s : S) (p : P1 s) (s' : S) => Q s (f s p) s']) ([P2, Q]) f).
  intros. unfold post. unfold subset. intros. trivial.
Qed.


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

Lemma refineSeqAssign : forall (f: S -> S) (g: S -> S) (h: S -> S),
  (forall (s : S), h s = g (f s)) -> 
  Assign h ⊑ Assign f ;; Assign g.
Proof.
  intros.
  unfold Assign,Seq. simpl.
  assert (d: pre ([fun _ : S => True, fun (s : S) (_ : True) (s' : S) => s' = h s]) ⊂
             pre ([fun s : S => sig (fun _ : True => forall t : S, t = f s -> True),
                   fun (s : S) (_ : sig (fun _ : True => forall t : S, t = f s -> True))
                   (s' : S) => exists t : S, ex (fun _ : t = f s => s' = g t)])).
  simpl. unfold subset. intros. apply exist. assumption. intros; assumption.
  apply (Refinement _ _ d).
  simpl in *. unfold subset in *. intros. inversion H0. inversion H1. rewrite H.
  rewrite <- x1. rewrite <- H2. reflexivity.
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

Definition While (inv : Pow S) (cond : S -> bool) (body : PT) : PT :=
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
Lemma refineWhile (inv : Pow S) (cond : S -> bool) : 
  let pt := [inv , fun _ _ s' => inv s' ] in
  let body := [fun s => inv s /\ Is_true (cond s), (fun _ _ s => inv s)] in
  pt ⊑ While inv cond body.
  Proof.
    intros; simpl in *.
    assert (d: pre pt ⊂ pre (While inv cond body)).
    unfold subset, pt,While; simpl; intros; split; [assumption | ].
    split.
    intros s' H1. 
    destruct H1; split; assumption.
    intros s' s'' [H1 H2] H3; assumption.
    apply (Refinement _ _ d).
    intros s PreS s' [H1 H2].
    assumption.
Qed.

Definition WhileSemantics  (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) : Type
  := inv s 
    /\ (forall s, Is_true (cond s) /\ inv s -> extend body inv s)
    /\ (forall s, Is_false (cond s) /\ inv s -> U s).

Lemma WhileExtendL (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) :
  extend (While inv cond body) U s -> WhileSemantics inv cond body U s.
  Proof.
    unfold extend; simpl; intros [[H1 [H2 H3] H4 ]].
    split; [ assumption | split].
    - intros s' [H5 H6].
      unfold extend; exists (H2 s' (conj H5 H6)); intros s'' H7; eapply H3; exact H7.
    - intros s' [A B]; apply H4; split; try assumption.
  Qed.

Lemma WhileExtendR (inv : Pow S) (cond : S -> bool) (body : PT) (U : Pow S) (s : S) :
  WhileSemantics inv cond body U s ->
    extend (While inv cond body) U s.
  Proof.
    unfold extend; intros [I [T F]]; simpl in *.
    split; [split; [assumption | ] | ].
    set (H := fun s Hs => projT1 (T s Hs)); exists H.
    intros; eapply (projT2 (T s0 t)); unfold H in *; assumption.
    intros s' [H1 H2]; apply F; split; assumption.
Qed.
    
    
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

End Refinement.

Module While.

Require Import EqNat.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Show.
Import Refinement.

Axiom (showNat : nat -> string).

Definition setN : nat -> S -> S := fun x s =>
  match s with
    | mkS _ p q r => mkS x p q r
  end.

Definition setP : nat -> S -> S := fun x s =>
  match s with
    | mkS n _ q r => mkS n x q r
  end.

Definition setQ : nat -> S -> S := fun x s =>
  match s with
    | mkS n p _ r => mkS n p x r
  end.

Definition setR : nat -> S -> S := fun x s =>
  match s with
    | mkS n p q _ => mkS n p q x
  end.

(* Identifiers *) 

Inductive Identifier : Type :=
  | N : Identifier
  | P : Identifier
  | Q : Identifier
  | R : Identifier.

Definition setIdent (ident: Identifier) (n : nat) : S -> S :=
  match ident with
  | N => setN n
  | P => setP n
  | Q => setQ n
  | R => setR n
end.

Definition getIdent (ident: Identifier) (s : S) : nat := 
  match ident , s with
  | N , mkS n _ _ _ => n
  | P , mkS _ p _ _ => p
  | Q , mkS _ _ q _ => q
  | R , mkS _ _ _ r => r
end.

(* Expressions *)

Inductive Expr : Type :=
  | Var    : Identifier -> Expr
  | EConst : nat -> Expr
  | Plus   : Expr -> Expr -> Expr
  | Minus  : Expr -> Expr -> Expr
  | Mult   : Expr -> Expr -> Expr
  | Div2   : Expr -> Expr.

Inductive BExpr : Type :=
  | BConst : bool -> BExpr
  | And    : BExpr -> BExpr -> BExpr
  | Or     : BExpr -> BExpr -> BExpr
  | Not    : BExpr -> BExpr
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
  | Div2 x    => div2 (evalExpr x s)
end.

Fixpoint evalBExpr (b: BExpr) (s: S) : bool :=
  match b with
  | BConst b  => b 
  | And b1 b2 => andb (evalBExpr b1 s) (evalBExpr b2 s) 
  | Or b1 b2  => orb (evalBExpr b1 s) (evalBExpr b2 s)
  | Not e     => negb (evalBExpr e s)
  | Eq e1 e2  => beq_nat (evalExpr e1 s) (evalExpr e2 s)
  | Lt e1 e2  => proj1_sig (nat_lt_ge_bool (evalExpr e1 s) (evalExpr e2 s))
  | Le e1 e2  => proj1_sig (nat_le_gt_bool (evalExpr e1 s) (evalExpr e2 s))
  | Gt e1 e2  => proj1_sig (nat_gt_le_bool (evalExpr e1 s) (evalExpr e2 s))
  | Ge e1 e2  => proj1_sig (nat_ge_lt_bool (evalExpr e1 s) (evalExpr e2 s))
end.

(* While Language *)

Inductive WhileL : Type :=
  | WSkip   : WhileL
  | WAssign : Identifier -> Expr -> WhileL
  | WSeq    : WhileL -> WhileL -> WhileL
  | WIf     : BExpr -> WhileL -> WhileL -> WhileL
  | WWhile  : Pow S -> BExpr -> WhileL -> WhileL
  | Spec    : PT -> WhileL.

Fixpoint semantics (w: WhileL) : PT :=
  match w with
  | WSkip          => Skip
  | WAssign id exp => Assign (fun s => (setIdent id (evalExpr exp s)) s)
  | WSeq st1 st2   => Seq (semantics st1) (semantics st2)
  | WIf c t e      => If (fun s => (evalBExpr c s)) (semantics t) (semantics e)
  | WWhile inv c b => While inv (fun s => (evalBExpr c s)) (semantics b)
  | Spec pt        => pt
end.

Definition wrefines w1 w2 := (semantics w1) ⊑ (semantics w2).

Notation "P1 ≤ P2" := (wrefines P1 P2) (at level 80) : type_scope.
  

Fixpoint isExecutable (w: WhileL) : Prop :=
  match w with 
  | WSkip          => True
  | WAssign id exp => True
  | WSeq st1 st2   => (isExecutable st1) /\ (isExecutable st2)
  | WIf c t e      => (isExecutable t) /\ (isExecutable e)
  | WWhile inv c b => isExecutable b
  | Spec pt        => False
end.

Open Local Scope string_scope.

Definition identToCode (ident: Identifier) : string :=
  match ident with
  | N => "n"
  | P => "p"
  | Q => "q"
  | R => "r"
  end.

Fixpoint exprToCode (e: Expr) : string :=
  match e with
  | Var n     => identToCode n
  | EConst n  => print_nat n
  | Plus x y  => exprToCode x ++ " + " ++ exprToCode y
  | Minus x y => exprToCode x ++ " - " ++ exprToCode y
  | Mult x y  => exprToCode x ++ " * " ++ exprToCode y
  | Div2 x    => exprToCode x ++ " / 2"
  end.

Fixpoint bExprToCode (e: BExpr) : string :=
  match e with
  | BConst b  => match b with 
                 | true  => "true"
                 | false => "false"
                 end
  | And b1 b2 => "(" ++ bExprToCode b1 ++ " && " ++ bExprToCode b2 ++ ")"
  | Or b1 b2  => "(" ++ bExprToCode b1 ++ " || " ++ bExprToCode b2 ++ ")"
  | Not e     => "!" ++ bExprToCode e
  | Eq e1 e2  => "(" ++ exprToCode e1 ++ " == " ++ exprToCode e2  ++ ")"
  | Lt e1 e2  => "(" ++ exprToCode e1 ++ " < " ++ exprToCode e2  ++ ")"
  | Le e1 e2  => "(" ++ exprToCode e1 ++ " <= " ++ exprToCode e2  ++ ")"
  | Gt e1 e2  => "(" ++ exprToCode e1 ++ " > " ++ exprToCode e2  ++ ")"
  | Ge e1 e2  => "(" ++ exprToCode e1 ++ " >= " ++ exprToCode e2  ++ ")"
  end.

Fixpoint sp (n: nat) : string := 
   match n with
   | 0 => ""
   | Datatypes.S n' => " " ++ (sp n')
end.

Lemma isExecSeq1 : forall w1 w2, isExecutable (WSeq w1 w2) -> isExecutable w1.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecSeq2 : forall w1 w2, isExecutable (WSeq w1 w2) -> isExecutable w2.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecThen : forall c t e, isExecutable (WIf c t e) -> isExecutable t.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecElse : forall c t e, isExecutable (WIf c t e) -> isExecutable e.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecBody : forall inv c b, isExecutable (WWhile inv c b) -> isExecutable b.
Proof. intros; assumption. Qed.

Fixpoint toCode (w: WhileL) (p: isExecutable w) (indent: nat) : string :=
  match w as w' return (isExecutable w' -> nat -> string) with
  | WSkip           => fun _ _  => ((sp indent) ++ "skip")
  | WAssign id exp  => fun _ _ => 
                       ((sp indent) ++ (identToCode id) ++ " := " ++ (exprToCode exp))
  | WSeq w1 w2      => fun p' i' => 
                       (toCode w1 (isExecSeq1 w1 w2 p') i') ++ ";\n" ++ 
                       (toCode w2 (isExecSeq2 w1 w2 p') i')
  | WIf c t e       => fun p' i' =>
                       (sp indent) ++ "if " ++ (bExprToCode c) ++ "\n" ++
                       (sp indent) ++ "then {\n" ++ 
                       (toCode t (isExecThen c t e p') (i'+4)) ++ " }\n" ++
                       (sp indent) ++ "else {\n" ++ 
                       (toCode e (isExecElse c t e p') (i'+4)) ++ " }"
  | WWhile inv c b  => fun p' i' =>
                       (sp indent) ++ "while " ++ (bExprToCode c) ++ "{\n" ++
                       (sp indent) ++ (toCode b (isExecBody inv c b p') (i'+4)) ++ " }"
  | Spec pt         => fun p' i' => match p' with 
                                    end
  end p indent.

Definition whileExample : WhileL :=
  WSeq WSkip (WSeq (WIf (BConst true) WSkip WSkip) (WAssign P (Plus (Var R) (Var Q)))).

Lemma whileExec : isExecutable whileExample.
  Proof. unfold isExecutable; simpl; auto. Qed.

Compute (toCode whileExample whileExec 0).

Ltac w2pt_apply t := unfold "≤",semantics; apply t.

Definition wrefineTrans (w2 w1 w3 : WhileL) : 
  w1 ≤ w2 -> w2 ≤ w3 -> w1 ≤ w3.
    w2pt_apply refineTrans.
  Defined.

Definition wrefineRefl (w : WhileL) :
  w ≤ w.
    w2pt_apply refineRefl.
  Defined.

End While.


Module Example.

Require Import Div2.
Require Import Even.
Require Import Arith.
Require Import Arith.Bool_nat.
Require Import AuxiliaryProofs.
Import Refinement.
Import While.

Definition square : nat -> nat := fun n => n * n.

Definition Inv : S -> Prop := fun X => square (varR X) <= varN X < square (varQ X).

Definition SPEC := 
  ([ (fun _ => True), fun _ _ X => square (varR X) <= varN X < square (1 + varR X)]).

Definition PT1 :=
  ([ fun _ => True, fun _ _ X => Inv X /\ 1 + varR X = varQ X]).

Ltac refine_post pt1 pt2 := apply (Refinement _ _ (fun s (y : pre pt1 s) => y : pre pt2 s)).

Definition WSPEC := Spec SPEC.

Definition WPT1 := Spec PT1.

Lemma step1 : WSPEC ≤ WPT1.
  Proof.    
    unfold WSPEC, WPT1, "≤", semantics. 
    unfold SPEC, PT1, Inv. refine_post SPEC PT1.
    intros X tt s [H1 H2]; simpl in *; rewrite H2; apply H1.    
  Qed.

Definition PT2 := [fun _ => True , K Inv] ;; 
                  [Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X].

Definition WPT2 := WSeq (Spec ([fun _ => True , K Inv])) (Spec ([Inv, fun _ _ X => Inv X /\ 1 + varR X = varQ X])).

Lemma step2 : WPT1 ≤ WPT2.
  Proof.
    unfold WPT1, WPT2, "≤", semantics. 
    unfold PT1, PT2, Inv, Seq. simpl.
    assert (d : forall s, pre PT1 s -> pre PT2 s).
    intros; exists I; intros; auto.
    apply (Refinement _ _ d).
    simpl; intros s Pre s' [t [H1 [H2 H3]]]; split; auto.
Qed.

Definition PT3a :=
  Assign (fun s => mkS (varN s) (varP s) (1 + (varN s)) 0).

Definition WPT3aa :=
  WAssign R (EConst 0).

Definition WPT3ab :=
  WAssign Q (Plus (EConst 1) (Var N)).

Definition WPT3a := WSeq WPT3aa WPT3ab.

Definition PT3b :=
  While Inv (fun X => negb (beq_nat (1 + varR X) (varQ X))).


Definition WPT3b :=
  let guard := (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) in
  WWhile Inv guard (Spec ([fun s => evalBExpr guard s = true /\ Inv s, 
                           fun _ _ s' => Inv s'])).

Lemma step3 : WPT2 ≤ WSeq WPT3a WPT3b.
Proof.
  unfold WPT2,WPT3a,WPT3aa,WPT3ab,WPT3b,"≤",semantics.
  simpl.
  apply refineSplit.
  unfold Assign, K, Inv.
  apply (refineTrans PT3a).
  (* Part a *)
    unfold K, Inv, PT3a, square; apply refineAssign.
    simpl; intros; split; auto with arith.
  (* refineTrans *)
  unfold PT3a,Assign.
  apply refineSeqAssign.
  intros; destruct s; simpl; reflexivity.
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

Definition WPT4 :=
  WSeq (Spec ([fun X => 1 + varR X < varQ X, fun _ _ X => varR X < varP X < varQ X]))
       (Spec ([fun X => varR X < varP X < varQ X /\ Inv X, fun _ _ X => Inv X])).

Lemma step4 : WPT3b ≤ WPT4.
  unfold WPT3b,WPT4,"≤",semantics.
  simpl.
  (* apply refineSeq. *)
Admitted.

Lemma step4' : PT3b ⊑ PT4.
  (* proceed by refining body of while? *)
  Admitted.
 

Definition PT5a :=
  Assign (fun s => setP (div2 (varQ s + varR s)) s).

Definition WPT5a :=
  WAssign P (Div2 (Plus (Var Q) (Var R))).

Definition PT5bThen := 
  [fun s => (varN s < square (varP s)) /\ (varP s < varQ s) /\ Inv s,
   fun _ _ s' => Inv s'].

Definition WPT5bThen := Spec PT5bThen.

Definition PT5bElse :=
  [fun s => (varN s >= square (varP s)) /\ (varR s < varP s) /\ Inv s,
   fun _ _ s' => Inv s'].

Definition WPT5bElse := Spec PT5bElse.

Definition PT5b :=
  If (fun s => proj1_sig (nat_lt_ge_bool (varN s) (square (varP s))))
    PT5bThen PT5bElse.

Definition WPT5b :=
  WIf (Lt (Var N) (Mult (Var P) (Var P))) WPT5bThen WPT5bElse.

Lemma step5 : WPT4 ≤ WSeq WPT5a WPT5b.
  unfold "≤",semantics. 
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
  unfold PT5bThen,PT5bElse, Inv.
  Check refineIf.
  
 
Admitted.

Lemma step6Then : PT5bThen ⊑ Assign (fun s => setQ (varP s) s). 
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  destruct s as [N P Q R]. unfold Inv.
  simpl in *. destruct H3 as [H3 H4]. destruct H3.
  split. 
  simpl in *. unfold square in *.

Admitted.

Lemma step6Else : PT5bElse ⊑ Assign (fun s => setR (varP s) s). 
  apply refineAssign.
  simpl.
  intros s H.
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  destruct s. unfold Inv.
  simpl in *. destruct H3 as [H3 H4]. simpl in *.
  split; auto.
Qed.

(* FIXME (WSkip) *)
Theorem result : WSPEC ≤ (
  WSeq WPT3a
  (WWhile Inv (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) WSkip)
  ).
Proof.
  apply (wrefineTrans WPT1). apply step1.
  apply (wrefineTrans WPT2). apply step2.
  apply (wrefineTrans (WSeq WPT3a WPT3b)). apply step3.
  apply refineRefl.
Qed.

Definition prgrm := WSeq WPT3a
  (WWhile Inv (Not (Eq (Plus (EConst 1) (Var R)) (Var Q))) WSkip).

Lemma prgrmProof : isExecutable prgrm.
Proof.  
  unfold prgrm,isExecutable; simpl; auto.
Qed.

Require Import String.
Compute (toCode prgrm prgrmProof 0).

Theorem result' : SPEC ⊑ 
  (
  PT3a ;; 
  While (PT5a ;; If (fun s => proj1_sig (nat_lt_ge_bool (varN s) (square (varP s))))
                   (Assign (fun s => setQ (varP s) s))
                   (Assign (fun s => setR (varP s) s)))
       (fun X => negb (beq_nat (1 + varR X) (varQ X)))
  ).
    apply (refineTrans PT1); try apply step1.
    apply (refineTrans PT2); try apply step2.
    apply (refineTrans (PT3a ;; PT3b)); try apply step3.
    apply refineRefl.  
Qed.

End Example.


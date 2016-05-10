Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Heap.
Module Language.

Definition Ptr := Addr.t.
Definition Pow : Type -> Type := fun a => a -> Prop.
Definition S := heap.

(* Extended PT to cover the return type  -- now the postcondition refers to the return value also *)
Inductive PT (a : Type) : Type :=
  Predicate : forall pre : Pow S, (forall s : S, pre s -> a -> Pow S) -> PT a.
(* We'll need to update the refinement relation between PTs too... *)

(* While Language *)

Inductive WhileL (a : Type) : Type :=
  | New    : forall v, v -> (Ptr -> WhileL a) -> WhileL a
  | Read   : forall v, Ptr -> (v -> WhileL a) -> WhileL a
  | Write : forall v, Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S -> Prop) -> bool -> WhileL a -> WhileL a (*TODO add variant *)
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "id ::= exp" := (Write id exp) (at level 52).

Definition trivial : forall a, PT a.
  intros; refine (Predicate _ (fun s => True) _); intros _ _ _ _; exact True.
Defined. (*this is a dummy PT -- don't ever use it*)

Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
  | Write _ v c => 
  | _ => trivial _
  end.
  | Read
  | Write
  | Assign id exp => Assign_PT (fun h => M.In id h) 
                               (fun s => (setIdent id (evalExpr exp s)) s)
  | While inv c b => While_PT inv (fun s => (evalBExpr c s)) (semantics b)
  | Spec pt       => pt
end.


Fixpoint bind {a b : Type} (w : WhileL a) (k : a -> WhileL b) {struct w} : WhileL b.
  refine (
  match w with
  | New _ v c  => New _ _ v (fun p => bind _ _ (c p) k)
  | Read _ p c => Read _ _ p (fun v => bind _ _ (c v) k)
  | Write _ p v c => Write _ _ p v (bind _ _ c k)
  | While Inv cond body => While _ Inv cond (bind _ _ body k)
  | Spec pt => Spec _ (Predicate _ _ _) 
      (*hmm I need to think about this branch. It should basically fold
      the seq rule we had previously into the existing spec 
      something along the lines of:
      Given pre : S -> Prop, post : forall s, pre s -> A -> S -> Prop,
      and k : a -> WhileL b
      Define a new spec consisting of
      - the precondition: 
          (h : pre s) /\ forall s' v, post s h v s' -> preconditionOf (k v)
      - the postcondition: forall s pres x s'',
        exists s' y, post s pres x s' /\ postConditionOf (k v) s' y s''
      where preconditionOf and postConditionOf project out the pre/post of
      the PT associated with a While by the semantics function above
       *)
  | Return x => k x
  end).
Admitted.
  
(* TODO Add other notations from Ynot, including 'bind' *)

(* Hmm, the isExecutable function now requires an initial heap...
In the branches for New and Read, we need to check that the 'continuations Ptr -> While and v -> While
do not produce specs... 
Fixpoint isExecutable (w: WhileL) : Prop :=
  match w with 
  | New _ _         => True
  | While inv c b => isExecutable b
  | Spec pt       => False
end.
*)
End Language.


Definition wrefines w1 w2 := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

Lemma refineAssign (w : WhileL) (id : Identifier) (exp : Expr) 
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre ((setIdent id (evalExpr exp s)) s)) (h' : pre (semantics w) ⊂ (fun h => M.In id h))
  : w ⊑ Assign id exp.
  Proof.
    assert (d: pre (semantics w) ⊂ pre (semantics (Assign id exp))); refine_simpl.
    apply (Refinement _ _ d).
    simpl; intros s pres s' [eq _]; rewrite eq; auto.
  Qed.


Definition subst (id : Identifier) (exp : Expr) (s : S) : S := 
   setIdent id (evalExpr exp s) s.

Lemma refineFollowAssign (id : Identifier) (exp : Expr) (P : Pow S) 
(Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec ([P,Q]) in
  let w' := Spec ([P,Q']) in
  (forall s pres s', Q' s pres s' -> prod (Q s pres (subst id exp s')) (M.In id s')) ->
  w ⊑ (w' ; id ::= exp).
Proof.
  intros w w' HQ.
  set (d := (fun (s : S) (H : P s) => 
              (exist (fun a => forall t : S, Q' s a t -> M.In id t) H 
                     (fun t' Ht => snd (HQ s H t' Ht)))) : 
             pre (semantics w) ⊂ pre (semantics (w' ; id ::= exp))).
(*
  set (d := (fun (s : S) (H : P s) => 
              (exist (fun a => forall t : S, Q' s a t -> True) H (fun _ _ => I))) : 
         pre (semantics w) ⊂ pre (semantics (w' ; id ::= exp))).*)
  apply (Refinement _ _ d).
  unfold subset; simpl; intros.
  inversion H as [s' H1].
  inversion H1 as [H2 [H3 H4]].
  rewrite H3.
  apply HQ.  
  assumption.
Qed.

Lemma refineSeq (Pre Mid Post : Pow S) :
  let w := Spec ([ Pre , fun _ _ s' => Post s' ]) in
  w ⊑ (Spec ([Pre , (fun _ _ s' => Mid s') ]) ; Spec ([Mid , (fun _ _ s' => Post s') ])).
Proof. 
  unfold "⊑",semantics; apply refineSeqPT.
Qed.

Definition refineTrans (w2 w1 w3 : WhileL) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold "⊑",semantics; apply refineTransPT.
  Defined.

Definition refineRefl (w : WhileL) :
  w ⊑ w.
    unfold "⊑",semantics; apply refineReflPT.
  Defined.

Lemma refineSeqAssocR : forall (w w1 w2 w3 : WhileL),
  (w ⊑ (w1 ; w2) ; w3) -> (w ⊑ w1 ; w2 ; w3).
Proof.
  intros.
  apply (refineTrans ((w1; w2); w3)).
  assumption.
  apply refineSeqAssocR_PT.
Defined.

Lemma refineSeqAssocL : forall (w w1 w2 w3 : WhileL),
  (w ⊑ w1 ; w2 ; w3) -> (w ⊑ (w1 ; w2) ; w3).
Proof.
  intros.
  apply (refineTrans (w1; w2; w3)).
  assumption.
  apply refineSeqAssocL_PT.
Defined.

Lemma refineIf (cond : BExpr) (pt : PT) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true (evalBExpr cond s)),
                     fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false (evalBExpr cond s)),
                     fun s pre s' => post pt s (fst pre) s' ] in
  (Spec pt) ⊑ If cond (Spec thenBranch) (Spec elseBranch).
Proof.
  unfold "⊑",semantics; apply refineIfPT.
Qed.

Lemma refineWhile (inv : Pow S) (cond : BExpr) (Q : Pow S) 
  (StrQ : forall s, Is_false (evalBExpr cond s) -> Q s) : 
  let w := Spec ([inv , fun _ _ s' => inv s' /\ Q s']) in
  let body := [fun s => inv s /\ Is_true (evalBExpr cond s), (fun _ _ s => inv s)] in
  w ⊑ While inv cond (Spec body).
  Proof.
    unfold "⊑",semantics; now (apply refineWhilePT).
Qed.

Definition refineSplit (w1 w2 w3 w4 : WhileL) :
  (w1 ⊑ w3) -> (w2 ⊑ w4) -> (w1 ; w2) ⊑ (w3 ; w4).
    unfold "⊑",semantics; apply refineSplitPT.
  Defined.

Definition refineSplitIf (w1 w2 w3 w4 : WhileL) (cond : BExpr) :
  (w1 ⊑ w3) -> (w2 ⊑ w4) -> If cond w1 w2 ⊑ If cond w3 w4.
    unfold "⊑",semantics; apply refineSplitIfPT.
  Defined.

Definition refineBody : forall (inv : Pow S) (cond : BExpr) (bodyL bodyR : WhileL),
  bodyL ⊑ bodyR ->
  While inv cond bodyL ⊑ While inv cond bodyR.
Proof.
  unfold "⊑",semantics.
  intros.
  assert (d: pre (semantics (While inv cond bodyL)) ⊂
             pre (semantics (While inv cond bodyR))).
  unfold subset; simpl; intros s [Inv [H1 H2]]; split.
  assumption.
  inversion H as [Pre Post].
  set (E := fun s0 H => (Pre s0 (H1 _ H))).
  exists E.
  intros s0 s' P Q.
  eapply H2.
  apply Post.
  unfold E in Q.
  exact Q.

  apply (Refinement _ _ d).
  intros.
  unfold post,pre,subset in *.
  simpl in *.
  intros; assumption.
Defined.

End Semantics.

Module CodeGeneration.

Import Language.
Import Heap.

Open Local Scope string_scope.

Definition t := Addr.t.

Definition identToCode (ident: Identifier) : string :=
  "x_" ++ (Addr.printAddr ident print_nat).

Fixpoint exprToCode (e: Expr) : string :=
  match e with
  | Var n     => identToCode n
  | EConst n  => print_nat n
  | Plus x y  => exprToCode x ++ " + " ++ exprToCode y
  | Minus x y => exprToCode x ++ " - " ++ exprToCode y
  | Mult x y  => exprToCode x ++ " * " ++ exprToCode y
  | Div2 x    => "(" ++ exprToCode x ++ ") / 2"
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

Lemma isExecSeq1 : forall w1 w2, isExecutable (Seq w1 w2) -> isExecutable w1.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecSeq2 : forall w1 w2, isExecutable (Seq w1 w2) -> isExecutable w2.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecThen : forall c t e, isExecutable (If c t e) -> isExecutable t.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecElse : forall c t e, isExecutable (If c t e) -> isExecutable e.
Proof. intros; destruct H as [H1 H2]; assumption. Qed.

Lemma isExecBody : forall inv c b, isExecutable (While inv c b) -> isExecutable b.
Proof. intros; assumption. Qed.

Fixpoint toCode (w: WhileL) (p: isExecutable w) (indent: nat) : string :=
  match w as w' return (isExecutable w' -> string) with
  | New x          => fun _ => "FIXME" (*fun _ => do n <- fresh; let varName = "x_" ++ show n ; return (varName ++ "=" ++ exprToCode x) *)
    (* FIXME: should not be x in the above line, but the freshly allocated address *)
  | Skip           => fun _ => ((sp indent) ++ "skip;")
  | Assign id exp  => fun _ => 
                      ((sp indent) ++ (identToCode id) ++ " = " ++ (exprToCode exp)) ++ ";"
  | Seq w1 w2      => fun p' => 
                      (toCode w1 (isExecSeq1 w1 w2 p') indent) ++ "
" ++ 
                      (toCode w2 (isExecSeq2 w1 w2 p') indent)
  | If c t e       => fun p' =>
                      (sp indent) ++ "if " ++ (bExprToCode c) ++ "
" ++
                      (sp indent) ++ "{
" ++ 
                      (toCode t (isExecThen c t e p') (indent+4)) ++ "
" ++
                      (sp indent) ++ "}
" ++
                      (sp indent) ++ "else 
" ++ 
                      (sp indent) ++ "{
" ++ 
                      (toCode e (isExecElse c t e p') (indent+4)) ++ "
" ++
                      (sp indent) ++ "}"
  | While inv c b  => fun p' =>
                      (sp indent) ++ "while (" ++ (bExprToCode c) ++ ")
" ++
                      (sp indent) ++ "{
" ++
                      (toCode b (isExecBody inv c b p') (indent+4)) ++ "
" ++
                      (sp indent) ++ "}"
  | Spec pt        => fun p' => match p' with 
                                end
  end p.

Definition wrapMain (code : string) : string :=
"int main() {
    int n,p,q,r;
" ++ code ++ "
    return 0;
}".

Definition whileToCode (w: WhileL) (p: isExecutable w) : string :=
  wrapMain (toCode w p 4).

End CodeGeneration.
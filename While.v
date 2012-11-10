Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Show.
Require Export Refinement.

Module Language.

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

(* While Language *)

Inductive WhileL : Type :=
  | Skip   : WhileL
  | Assign : Identifier -> Expr -> WhileL
  | Seq    : WhileL -> WhileL -> WhileL
  | If     : BExpr -> WhileL -> WhileL -> WhileL
  | While  : Pow S -> BExpr -> WhileL -> WhileL
  | Spec   : PT -> WhileL.

Notation "w1 ; w2" := (Seq w1 w2) (at level 52, right associativity).
Notation "id ::= exp" := (Assign id exp) (at level 52).

Fixpoint isExecutable (w: WhileL) : Prop :=
  match w with 
  | Skip          => True
  | Assign id exp => True
  | Seq st1 st2   => (isExecutable st1) /\ (isExecutable st2)
  | If c t e      => (isExecutable t) /\ (isExecutable e)
  | While inv c b => isExecutable b
  | Spec pt       => False
end.

(*
Extraction Language Haskell.
Extraction "While.hs" WhileL.
*)
End Language.

Module Semantics.

Import Language.

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

Fixpoint semantics (w: WhileL) : PT :=
  match w with
  | Skip          => Skip_PT
  | Assign id exp => Assign_PT (fun s => (setIdent id (evalExpr exp s)) s)
  | Seq st1 st2   => Seq_PT (semantics st1) (semantics st2)
  | If c t e      => If_PT (fun s => (evalBExpr c s)) (semantics t) (semantics e)
  | While inv c b => While_PT inv (fun s => (evalBExpr c s)) (semantics b)
  | Spec pt       => pt
end.

Definition wrefines w1 w2 := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

Lemma refineAssign (w : WhileL) (id : Identifier) (exp : Expr) 
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre ((setIdent id (evalExpr exp s)) s))

  : w ⊑ Assign id exp.
  Proof.
    assert (d: pre (semantics w) ⊂ pre (semantics (Assign id exp))); refine_simpl.
    apply (Refinement _ _ d).
    simpl; intros s pres s' eq; rewrite eq; auto.
  Qed.

(* TODO: law for multiple assignments? *)
Lemma refineSeqAssign : forall (id id1 id2 : Identifier) (exp exp1 exp2 : Expr),
  let setEval id exp s := (setIdent id (evalExpr exp s) s) in
  let WAssign := Assign id exp in
  let WAssignSeq := Assign id1 exp1 ; Assign id2 exp2 in
  (forall (s : S), setEval id exp s = setEval id2 exp2 (setEval id1 exp1 s)) -> 
  WAssign ⊑ WAssignSeq.
Proof.
  intros.
  assert (d: pre (semantics (WAssign)) ⊂ pre (semantics (WAssignSeq))). 
  refine_simpl.
  intros; apply exist.
  assumption. 
  intros; assumption.
  apply (Refinement _ _ d).
  simpl in *; unfold subset in *. 
  intros; inversion H0; inversion H1.
  rewrite H2.
  rewrite x1.
  symmetry; apply H.
Qed.

Definition subst (id : Identifier) (exp : Expr) (s : S) : S := 
   setIdent id (evalExpr exp s) s.

(* TODO: Finish this *)
Lemma refineFollowAssign (id : Identifier) (exp : Expr) (P : Pow S) 
(Q Q' : forall (s : S), P s -> Pow S) :
  let w  := Spec ([P,Q]) in
  let w' := Spec ([P,Q']) in
  (forall s pres s', Q' s pres s' -> Q s pres (subst id exp s')) ->
  w ⊑ (w' ; id ::= exp).
Proof.
  intros w w' HQ.
  assert (d: pre (semantics w) ⊂ pre (semantics (w' ; id ::= exp))).
  unfold subset; simpl; intros. 
  exists H; intros; trivial. 
  apply (Refinement _ _ d).  
  unfold subset; simpl; intros.
  inversion H as [s' H1].
  inversion H1 as [H2 H3].
  rewrite H3.
  apply HQ.  
Admitted.

Lemma refineSeq (Pre Mid Post : Pow S) :
  let w := Spec ([ Pre , fun _ _ s' => Post s' ]) in
  w ⊑ (Spec ([Pre , (fun _ _ s' => Mid s') ]) ; Spec ([Mid , (fun _ _ s' => Post s') ])).
Proof. 
  unfold "⊑",semantics; apply refineSeqPT.
Qed.

(* TODO: Finish this *)
Lemma refineSeqAssocR : forall (w w1 w2 w3 : WhileL),
  (w ⊑ (w1 ; w2) ; w3) -> (w ⊑ w1 ; w2 ; w3).
Proof.
  intros w w1.
  unfold wrefines.
  simpl.
  induction w1.
  destruct w2.
  simpl.
  unfold Skip_PT, Seq_PT.
  simpl.
  intros.
Admitted.

(* TODO: Finish this *)
Lemma seqAssoc : forall (w1 w2 w3 : WhileL),
  semantics (w1 ; w2 ; w3) = semantics ((w1 ; w2) ; w3).
Proof.
  intros w1.
  induction w1.
  simpl.
  destruct w2.
  simpl.
  unfold Skip_PT,Seq_PT.
  simpl.
  intros.
Admitted.

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

Definition refineTrans (w2 w1 w3 : WhileL) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold "⊑",semantics; apply refineTransPT.
  Defined.

Definition refineRefl (w : WhileL) :
  w ⊑ w.
    unfold "⊑",semantics; apply refineReflPT.
  Defined.

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
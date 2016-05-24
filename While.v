Require Import EqNat.
Require Import Bool.
Require Import String.
Require Import Arith.Bool_nat.
Require Import Div2.
Require Import Heap.
Require Import RefinementNew.
Require Import Program.Tactics.
Module Language.

Definition Ptr := Addr.t.

Inductive WhileL (a : Type) : Type :=
  | New    : forall v, v -> (Ptr -> WhileL a) -> WhileL a
  | Read   : forall v, Ptr -> (v -> WhileL a) -> WhileL a
  | Write : forall v, Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S -> Prop) -> (S -> bool) -> WhileL a -> WhileL a (*TODO add variant *)
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "id ::= exp" := (Write id exp) (at level 52).

(* Joao: is this strong enough? or should we add to the post-condition "find s p = None" ? *)
(* Wouter: we could add this... but that would only be useful if we wanted to access unallocated memory... *)
Definition NewPT {a : Type} (x : a) : PT Ptr :=              
  Predicate _ (fun s => True) (* trivial precondition *)
              (fun s _ p s' => (* given initial state s, result pointer p, and final state s' *)
                 (forall p', p' <> p -> find s p = find s' p') (* all existing addresses are unmodified *)
                 /\ find s' p = Some (dyn _ x)). (* and the heap now lets p point to x *)

Definition ReadPT {a : Type} (ptr : Ptr) : PT a :=
  Predicate _ (fun s => exists v, find s ptr = Some (dyn a v)) (* if there is a value for the ptr *)
              (fun s pres v s' => s = s' /\ find s ptr = Some (dyn a v)). (* we need to return this value and leave the heap untouched *)
(* The postcondition here is slightly crappy -- any ideas? We can't project from the exists as it is in Prop *)
(* Joao: Not really. Unless we change PT def with a precondition like S -> (Prop,a). *)

(* I'm slightly doubting whether or not it is going to work in the first place -- 
   the bool is necessary a constant that does not depend on the state.
   Perhaps having a condition: Heap -> bool is better? *)
(* Joao: I think so. what about using While_PT instead? (defined below, based on our old definition  *)
(* Wouter: Yes, let's use this While_PT *)
Definition Is_false (b : bool) :=
  match b with
    | true => False
    | false => True
  end.

Definition WhilePT {a : Type} (inv : Pow S) (cond : S -> bool) (body : PT a) : PT a :=
  let whilePre := (fun s =>   (* The invariant should hold initially *)
                             inv s /\ 
                              (* If we enter the loop, the precondition of the body should hold *)
                            { H : (forall s, Is_true (cond s) /\ inv s -> pre body s) &
                              (* The loop body should preserve the invariant *)
                            (forall s v s' (t : Is_true (cond s) /\ inv s), post body s (H s t) v s' -> inv s')})                          
  in
  let whilePost := (fun _ _ _ s' => inv s' /\ Is_false (cond s')) in
  [ whilePre , whilePost ].



Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
    | New _ _ v k => BindPT (NewPT v) (fun p => semantics (k p))
    | Read _ _ ptr k => BindPT (ReadPT ptr) (fun v => semantics (k v))
    | Write _ _ ptr v k => 
      SeqPT (AssignPT (fun h => M.In ptr h) (fun s => (update s ptr (dyn _ v))))
             (semantics k)            
    | While _ inv c body => WhilePT inv c (semantics body)
    | Spec _ s => s
    | Return _ x => Predicate _ (fun s => True) (fun s _ v s' => s = s' /\ v = x)
  end.

Definition preConditionOf {a : Type} (w : WhileL a) : Pow S :=
  match semantics w with
    | Predicate _ p _ => p
  end.

Definition postConditionOf {a : Type} (w : WhileL a)
  : (forall s : S, preConditionOf w s -> a -> Pow S) :=
  match semantics w as x return (forall s : S, match x with | [p, _] => p end s -> a -> Pow S) with
    | [pre, post] => post
  end.

Fixpoint bind {a b : Type} (w : WhileL a) (k : a -> WhileL b) {struct w} : WhileL b :=
  match w with
  | New _ _ v c  => New _ _ v (fun p => bind (c p) k)
  | Read _ _ p c => Read _ _ p (fun v => bind (c v) k)
  | Write _ _ p v c => Write _ _ p v (bind c k)
  | While _ Inv cond body => While _ Inv cond (bind body k)
  | Spec _ pt => Spec _
        match pt with
        | [pre, post] =>
            [fun s : S => {h : pre s | forall (s' : S) (v : a), post s h v s' -> preConditionOf (k v) s'},
            fun (s : S)
              (h : {h : pre s |
                     forall (s' : S) (v : a),
                       post s h v s' -> preConditionOf (k v) s'}) 
              (y : b) (s'' : S) =>
            exists (s' : S) (x : a),
              {p : post s (proj1_sig h) x s' |
              postConditionOf (k x) s' (proj2_sig h s' x p) y s''}]
        end
  | Return _ x => k x
  end.

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ _ _ k     => forall ptr, isExecutable (k ptr)
    | Read _ _ _ k    => forall v, isExecutable (k v)
    | Write _ _ _ _ w => isExecutable w
    | While _ inv c b => isExecutable b
    | Spec _ pt       => False
    | Return _ a      => True
  end.

Definition wrefines {a : Type} (w1 w2 : WhileL a) := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

(* Wouter: Do you want to finish these definitions? *)

Ltac refine_simpl := unfold semantics, pre, post, BindPT, NewPT, ReadPT, AssignPT, WhilePT, bind; simpl; destruct_conjs; subst.

Lemma refineAssign {a : Type} (w : WhileL unit) (ptr : Ptr) (x : a)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre tt (update s ptr (dyn a x)))
  (h' : pre (semantics w) ⊂ (fun h => M.In ptr h))
  : w ⊑ Write _ _ ptr x (Return _ tt).
  Proof.
    assert (d: pre (semantics w) ⊂ pre (semantics (Write _ _ ptr x (Return _ tt)))).
    Focus 2.
    apply (Refinement _ _ d).
    simpl; intros s pres u s' H.
    destruct_conjs; subst.
    rewrite <- H2.
    destruct u; apply (h s pres).
    destruct (semantics w).  simpl. unfold subset; split; now intuition.
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
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
  | Write : forall {v}, Ptr -> v -> WhileL a  -> WhileL a
  | While  : (S -> Prop) -> (S -> bool) -> WhileL a -> WhileL a (*TODO add variant *)
  | Spec   : PT a -> WhileL a
  | Return : a -> WhileL a.

Notation "addr ≔ exp" := (Write id addr) (at level 52).

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

Ltac pt_trivial := unfold subset in *; intros; now eauto.

Definition refineTransPT {a} (pt2 pt1 pt3 : PT a) : 
  pt1 ⊏ pt2 -> pt2 ⊏ pt3 -> pt1 ⊏ pt3.
    intros [pre12 post12] [pre23 post23].
    set (d (s : S) (pre1s : pre pt1 s) := pre23 s (pre12 s pre1s)).
    refine (Refinement pt1 pt3 d _); pt_trivial.
  Defined.

Definition refineReflPT {a} (pt : PT a) : pt ⊏ pt.
  refine (Refinement pt pt (fun s pres => pres) _); pt_trivial.
  Defined.

Fixpoint semantics {a : Type} (w: WhileL a) : PT a :=
  match w with
    | New _ _ v k => BindPT (NewPT v) (fun p => semantics (k p))
    | Read _ _ ptr k => BindPT (ReadPT ptr) (fun v => semantics (k v))
    | Write _ ptr v k => 
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
  | Write _ p v c => Write _ p v (bind c k)
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

Notation "a ; b" := (bind a (fun _ => b)) (at level 60).

Fixpoint isExecutable {a : Type} (w: WhileL a) : Prop :=
  match w with 
    | New _ _ _ k     => forall ptr, isExecutable (k ptr)
    | Read _ _ _ k    => forall v, isExecutable (k v)
    | Write _ _ _ w   => isExecutable w
    | While _ inv c b => isExecutable b
    | Spec _ pt       => False
    | Return _ a      => True
  end.

Definition wrefines {a : Type} (w1 w2 : WhileL a) := (semantics w1) ⊏ (semantics w2).

Notation "P1 ⊑ P2" := (wrefines P1 P2) (at level 90, no associativity) : type_scope.

Ltac unfold_refinements := unfold wrefines, semantics, preConditionOf, postConditionOf.

Definition refineTrans {a} (w2 w1 w3 : WhileL a) : 
  w1 ⊑ w2 -> w2 ⊑ w3 -> w1 ⊑ w3.
    unfold_refinements; now apply refineTransPT.
  Defined.

Definition refineRefl {a} (w : WhileL a) :
  w ⊑ w.
    unfold_refinements; apply refineReflPT.
  Defined.

Lemma refineBind {a} (Pre : Pow S) (Mid Post : a -> Pow S) :
  let w := Spec _ ([ Pre , fun _ _ => Post ]) in
  w ⊑ bind (Spec _ ([Pre , fun _ _ => Mid ]))
           (fun a => Spec _ ([Mid a , fun _ _ => Post ])).
Proof.
  unfold_refinements; simpl.
  assert (d : pre ([Pre, fun (s : S) (_ : Pre s) => Post]) ⊂
       pre ([fun s : S =>
      {_ : Pre s | forall (s' : S) (v : a), Mid v s' -> Mid v s'},
     fun (s : S)
       (_ : {_ : Pre s | forall (s' : S) (v : a), Mid v s' -> Mid v s'})
       (y : a) (s'' : S) =>
       exists (s' : S) (x : a), {_ : Mid x s' | Post y s''}])).
  unfold subset; simpl in *; destruct_conjs; intros; split; auto.
  apply (Refinement _ _ d).  
  unfold post, subset; intros; destruct_conjs; now trivial.
Qed.


Lemma refineSeq {a} (Pre Mid Post : Pow S) :
  let w := Spec a ([ Pre , fun _ _ _ => Post ]) in
  w ⊑ bind (Spec a ([Pre , fun _ _ _ => Mid ]))
           (fun _ => Spec a ([Mid , fun _ _ _ => Post ])).
Proof.
  apply refineBind.
Qed.

Lemma refineIf {a} (cond : bool) (pt : PT a) :
  let branchPre (P : S -> Prop) := fun s => prod (pre pt s) (P s) in
  let thenBranch := [branchPre (fun s => Is_true cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  let elseBranch := [branchPre (fun s => Is_false cond),
                     fun s pre s' => post pt s (fst pre) s' ] in
  (Spec a pt) ⊑ if cond then (Spec a thenBranch) else (Spec a elseBranch).
Proof.
  unfold_refinements; destruct cond; simpl.
  (* Joao: do we want this refinement rule? *)
  (* Wouter: why wouldn't we? *)
Admitted.

Lemma refineWhilePT {a} (inv : Pow S) (cond : S -> bool) (Q : Pow S) : 
  let pt := [inv , fun _ _ _ s' => inv s' /\ Q s'] in
  let body : PT a := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  (forall s, Is_false (cond s) -> Q s) ->
  pt ⊏ WhilePT inv cond body.
  Proof.
    intros pt body QH; simpl in *.
    assert (d: pre pt ⊂ pre (WhilePT inv cond body)).
    unfold subset, pt,WhilePT; simpl; intros; split; [assumption | ].
    split.
    intros s' H1. 
    destruct H1; split; assumption.
    intros s' v s'' [H1 H2] H3; assumption.
    apply (Refinement _ _ d).
    intros s PreS v' s' [H1 H2].
    split; [ | apply QH]; assumption.
Qed.

Lemma refineWhile {a} (inv : Pow S) (cond : S -> bool) (Q : Pow S) 
  (StrQ : forall s, Is_false (cond s) -> Q s) : 
  let w := Spec a ([inv , fun _ _ _ s' => inv s' /\ Q s']) in
  let body := [fun s => inv s /\ Is_true (cond s), (fun _ _ _ s => inv s)] in
  w ⊑ While a inv cond (Spec a body).
  Proof.
    unfold "⊑",semantics.
    now (apply refineWhilePT).
Qed.


Ltac destruct_unit :=
  match goal with
    [ H : unit |- _ ] => destruct H
  end.

Ltac destruct_units := repeat destruct_unit.
Ltac refine_simpl := unfold pre, post, subset; intros; simpl in *; destruct_conjs; repeat split; repeat subst; destruct_units.
Ltac semantic_trivial := unfold semantics, pre, post; simpl; destruct_conjs; repeat split; now intuition.

Lemma refineAssign {a : Type} (w : WhileL unit) (ptr : Ptr) (x : a)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre tt (update s ptr (dyn a x)))
  (h' : pre (semantics w) ⊂ (fun h => M.In ptr h))
  : w ⊑ Write _ ptr x (Return _ tt).
  Proof.
    assert (d: pre (semantics w) ⊂ pre (semantics (Write _ ptr x (Return _ tt)))).
    destruct (semantics w); semantic_trivial.
    apply (Refinement _ _ d); refine_simpl.
    destruct (semantics w); now eapply h.
  Qed.

(* Joao: (TODO) still missing the refinement rules for Read/Write/New/Return

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

<<<<<<< HEAD
=======
Lemma refineAssign {a} (w : WhileL a)
  (h : forall (s : S) (pre : pre (semantics w) s), post (semantics w) s pre ((setIdent id (evalExpr exp s)) s)) (h' : pre (semantics w) ⊂ (fun h => M.In id h))
  : w ⊑ Assign id exp.
>>>>>>> 6153f5ebe4855668de41d7e1633199f3151e3438

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
*)  
  
(** Just a brief example showing how the language currently looks like **)
  
Definition P : Addr.t := Addr.MkAddr 0.
Definition Q : Addr.t := Addr.MkAddr 1.
Definition N : Addr.t := Addr.MkAddr 2.

Definition SWAP {a} := 
  Spec a ([ fun s => M.In P s /\ M.In Q s /\ M.In N s
             , fun s _ _ s' => find s P = find s' Q
                            /\ find s Q = find s' P
                            /\ M.In P s' 
                            /\ M.In Q s'
                            /\ M.In N s']). 

Definition skip {a} : WhileL a := Spec a Skip_PT.

Definition swapResult {a} :
  let SetQinN (s : WhileL a) := (Read _ a Q) (fun v => Write _ N v s) in
  let SetPinQ (s : WhileL a) := (Read _ a P) (fun v => Write _ Q v s) in
  let SetNinP (s : WhileL a) := (Read _ a N) (fun v => Write _ P v s) in
  SWAP ⊑ SetQinN (SetPinQ (SetNinP skip)).
  simpl.
  (* SWAP ⊑ (N ::= Var Q ; Q ::= Var P ; P ::= Var N) *)
Proof.
Admitted.

(** End of example **)

(* Joao: I stopped here *)

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
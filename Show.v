Require Import String.
Require Import Program.
Require Import Euclid.
Require Import Arith.
Require Import Omega.
Require Import Recdef.

Open Local Scope string_scope.

Program Definition print_digit (x : nat | x < 10) : string :=
 match proj1_sig x with
   | 0 => "0"
   | 1 => "1"
   | 2 => "2"
   | 3 => "3"
   | 4 => "4"
   | 5 => "5"
   | 6 => "6"
   | 7 => "7"
   | 8 => "8"
   | 9 => "9"
   | _ => !
 end.

Ltac exfalso_refl :=
 match goal with [ H : ?X <> ?X |- _ ] => exfalso; apply H; reflexivity end.

Next Obligation.
 do 10 (destruct x as [ | x]; [ exfalso_refl | ]).
 refine (le_not_lt _ _ _ H9).
 omega.
Qed.

Next Obligation.
 do 9 (split; [intros F; discriminate F | ]).
 intros F; discriminate F.
Qed.

Program Fixpoint print_nat (x : nat) { measure x } : string :=
 match eucl_dev 10 _ x with
   | divex q r H1 H2 =>
     match q with
       | 0 => print_digit r
       | S _ => print_nat q ++ print_digit r
     end
 end.

Next Obligation.
 omega.
Defined.

Next Obligation.
 program_simpl; omega.
Defined.

(* Compute (print_nat 434). *)
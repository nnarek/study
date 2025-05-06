From Coq Require Export Arith.
Require Import Program.Wf.
Require Import Coq.Program.Tactics.
Require Import Coq.Init.Wf.

Program Fixpoint trivial_program_fixpoint (n : nat) {measure n}: nat :=
  match n with
    0 => 0
  | m => m
  end.
Check trivial_program_fixpoint.

(* #[global] Obligation Tactic := program_simpl. *)
#[global] Obligation Tactic := intros.


Program Fixpoint trivial_program_fixpoint' (n : nat): nat :=
  match n with
    0 => 0
  | m => m
  end.
Next Obligation.
  intuition. discriminate.
Qed.
Check trivial_program_fixpoint'.

Program Fixpoint trivial_program_fixpoint2 (n : nat) {measure n}: nat :=
  match n with
    0 => 0
  | m => m
  end.
Next Obligation.
  intuition. discriminate.
Qed.
Next Obligation.
  unfold well_founded,MR.
  intros.
  intuition. 
Qed.
Check trivial_program_fixpoint2.


Program Fixpoint trivial_program_fixpoint3 (l : list nat) {measure (length l)}: (list nat) := 
  match l with
  | nil => nil
  | l' => l'
  end.
Next Obligation.
  intuition. discriminate.
Qed.
Next Obligation.
  unfold well_founded,MR.
  intros.
  intuition. 
Qed.
Check trivial_program_fixpoint3.


Program Fixpoint countdown (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => countdown n'
  end.


(* Define a well-founded relation *)
Definition my_custom_order (n m : nat) := n < m.

(* Prove that it's well-founded *)
Lemma my_custom_order_wf : well_founded my_custom_order.
Proof.
  unfold my_custom_order.
  apply Wf_nat.lt_wf.
Qed.

(* Use this relation as a measure *)
Program Fixpoint countdown_custom (n : nat) {wf my_custom_order n} : nat :=
  match n with
  | 0 => 0
  | S n' => countdown_custom n'
  end.
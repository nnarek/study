Require Import Arith.

Print nat_ind.

Print nat_rect.

Definition prev : nat -> nat :=
    nat_rect 
        (fun _ => nat) (* here we specify return type of this function *)
        0 (* value of "prev 0" *)
        (fun n prevn => n). (* here we should return value for "prev (S n)" *)

Compute prev 0.
Compute prev 1.
Compute prev 2.

Definition factorial : nat -> nat :=
    nat_rect 
        (fun _ => _)
        1
        (fun n facn => (S n) * facn).

Compute factorial 0.
Compute factorial 1.
Compute factorial 2.
Compute factorial 3.

Definition add : nat -> nat -> nat :=
    nat_rect
        (fun _ => (nat -> nat))
        (fun b => b)
        (fun (a: nat) (adda: nat -> nat) b => S (adda b)).

Compute add 0 0.
Compute add 1 0.
Compute add 2 3.
Compute add 3 5.


(* is it possible to create language without rules of fixpoint and instead use axioms of inductive types and define match expression and fixpoint as syntactic sugar? *)
(* to do that we need to define how nat_rect should be evaluated *)
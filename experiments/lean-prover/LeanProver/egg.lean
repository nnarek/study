import Egg
import Mathlib.Data.Real.Basic
import Mathlib
example : 0 = 0 := by
  egg

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

open List in
example (α : Type) (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil  => egg [reverse_nil, append_nil, List.append]
  | cons head tail tail_ih => egg [*, append_assoc, reverse_cons, List.append]
-- adding ? sign at the end of egg will generate code which will not depend from Egg package
-- we need to add "head tail tail_ih" params manually,without them, egg will generate code with tail✝ head✝ unbound variables


set_option maxHeartbeats 300000
set_option egg.subgoals true
set_option egg.timeLimit 1

open Nat


attribute [egg real]
/- +     -/ add_comm add_assoc add_zero
/- -     -/ sub_zero zero_sub sub_self
/- *     -/ mul_comm mul_assoc mul_zero mul_one
/- /     -/ div_one zero_div
/- + /   -/ add_div
/- * /   -/ mul_div_mul_left mul_div_mul_right mul_div_mul_comm div_mul_div_cancel
            _root_.div_mul_div_comm div_mul_eq_div_mul_one_div
/- + -   -/ sub_sub sub_add add_sub add_comm_sub sub_add_cancel sub_add_eq_add_sub add_sub_assoc
/- + * / -/ left_distrib right_distrib add_div_eq_mul_add_div
/- ^     -/ pow_two pow_succ pow_zero pow_one


variable (x y : Real)

theorem freshmans_dream₂ : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  -- egg +real [Nat.succ_eq_add_one]
    sorry

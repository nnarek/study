import Mathlib.Data.Nat.Defs
open Nat


@[simp]
theorem A_to_B (x : ℕ) : x + 0 = x := by sorry

@[simp]
theorem B_to_A (x : ℕ) : x = x + 0 := by sorry

example (x : ℕ) : x + 0 = x := by
  simp -- Infinite loop or depth error



@[simp]
theorem A_to_B' (x : ℕ) : x + 0 ≥ x -> x ≥ x := by sorry

example (x : ℕ) : x ≥ x := by
  simp only [A_to_B'] -- simp does not work with implication
--TODO but I remember that lean able to simplify and completely prove implication

example (x : ℕ) : x + 0 ≥ x -> x ≥ x := by
  simp only [A_to_B']

import Mathlib.Logic.Basic
import Mathlib.Tactic

variable (P Q : Prop)

theorem hh : ¬ (¬ P) -> P := by
  intro h
  push_neg at h
  exact h

#print hh
#print Mathlib.Tactic.PushNeg.not_not_eq
#print propext

theorem hh' : ¬ (¬ P) -> P := by
  intro h
  by_contra
  apply h
  assumption

#print hh'
#print Classical.byContradiction
#print Decidable.byContradiction
#print Decidable.byCases
--TODO this theorems require that P should be decidable, but it is not decidable but I am able to call that theorems


theorem hh'' (a b: ℕ) : ¬ (¬ a = b) <-> a = b := by
  constructor <;> intro h
  · push_neg at h
    assumption
  · intro h'
    apply h' h

#print hh''
#print Mathlib.Tactic.PushNeg.not_not_eq

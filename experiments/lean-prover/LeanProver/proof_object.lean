import Mathlib.Data.Nat.Defs
open Nat


theorem double_elim (P : Prop) : (¬ ¬ P) <-> P := by simp
#print double_elim

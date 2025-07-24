import Mathlib.Data.Quot
import Mathlib.Tactic
open Quot
open Tactic


def mod4Rel (x y : Nat) : Prop :=
  x % 4 = y % 4

#check (Quot mod4Rel : Type)
#check (Quot.mk mod4Rel 2 : Quot mod4Rel)

def f (x : Nat) : Bool :=
  x % 4 = 0

-- only allow to do computation which return same thing on equivalent arguments
-- Quot.lift require to provide proof
theorem f_respects (a b : Nat) (h : mod4Rel a b) : f a = f b := by
  simp [mod4Rel, f] at *
  rw [h]

#check (Quot.lift f f_respects : Quot mod4Rel → Bool)

example (a : Nat) : Quot.lift f f_respects (Quot.mk mod4Rel a) = f a :=
  rfl


-- we can not get exact value from Quot
def get_nat (q: Quot mod4Rel) : Nat := by
  apply Quot.lift (fun x ↦ x) _ q
  simp
  unfold mod4Rel
  intro a b m
  sorry
  -- abort



def get_nat_mod2 (q: Quot mod4Rel) : Nat := by
  apply Quot.lift (fun x ↦ x%2) _ q
  dsimp
  intro a b m
  rw [←@Nat.mod_mod_of_dvd 2 4 a (by norm_num)]
  rw [←@Nat.mod_mod_of_dvd 2 4 b (by norm_num)]
  rw [m]

#eval get_nat_mod2 (Quot.mk mod4Rel 3) -- able to evaluate
#print get_nat_mod2
#print Quot.lift --have no definition

-- seems like kernel of lean have special reduction rule for lift function
-- TODO understand does cubical type theory allow to define quotient as HIT and do computation without special reduction rules

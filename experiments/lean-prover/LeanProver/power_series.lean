import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Basic

open PowerSeries


-- 1+x+x^2+x^3+... = 1/(1-x)
theorem geometric_series_eq {A : Type*} [Field A] : PowerSeries.mk (fun _ ↦ 1) = (1 - (X:A⟦X⟧))⁻¹ := by
  simp only [map_one, map_sub, constantCoeff_X, sub_zero, ne_eq,
            one_ne_zero, not_false_eq_true, PowerSeries.eq_inv_iff_mul_eq_one]
  ext n
  simp [coeff_mul,coeff_X]
  rw[Finset.filter_snd_eq_antidiagonal n 1,Finset.filter_snd_eq_antidiagonal n 0]
  cases' n <;> simp

--here is shorter proof from https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/PowerSeries/WellKnown.lean#L74
theorem mk_one_mul_one_sub_eq_one {A : Type*} [Field A]  : (mk 1 : A⟦X⟧) * (1 - X) = 1 := by
  rw [mul_comm, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [sub_mul]



def fib {A : Type*} [Field A] (n:Nat):= 
  if n <= 1 then (1:A)
  else fib (n-2) + fib (n-1)

theorem fib_series_eq {A : Type*} [Field A] : PowerSeries.mk fib = (1 - (X:A⟦X⟧) - X^2)⁻¹ := by
  simp only [map_one,map_sub, constantCoeff_X, sub_zero, map_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_ne_zero,
    PowerSeries.eq_inv_iff_mul_eq_one]
  ext n
  simp[coeff_mul,coeff_X,coeff_X_pow]
  unfold fib
  simp
  
  sorry


--using classical choose axiom,define power series which satisfy to the g(x)=1+x*g(x) recursive relation

theorem rec_geometric_series_exists (A : Type*) [Field A] : ∃ rs : A⟦X⟧, rs = 1 + X * rs := by
  use (1 - X)⁻¹
  symm
  simp only [map_sub, constantCoeff_one, constantCoeff_X, sub_zero, ne_eq, one_ne_zero,
    not_false_eq_true, PowerSeries.eq_inv_iff_mul_eq_one, add_mul, one_mul, mul_assoc,
    PowerSeries.inv_mul_cancel, mul_one, sub_add_cancel]

noncomputable def rec_geometric_series (A : Type*) [Field A] : A⟦X⟧ := Classical.choose (rec_geometric_series_exists A)


theorem rec_geometric_series_eq {A : Type*} [Field A] : PowerSeries.mk (fun _ ↦ 1) = rec_geometric_series A := by
  sorry

--composition of two power series
theorem ps_subst {A : Type*} [Field A] : (X:A⟦X⟧).subst X = (X:A⟦X⟧) := by
  rw [subst_X]
  exact PowerSeries.HasSubst.X'


-- TODO above one is easy because we can construct analytical solutions (1 - X)⁻¹, but it is hard to find non-recursive generating function for below one
-- maybe we can try to prove existance without providing actual instance of PW or instances of its coefficients 
-- f(x) = 1 + x * f(x * f(x))
theorem rec_pw_f_exists (A : Type*) [Field A] : ∃ f : A⟦X⟧, f = 1 + X * (f.subst (X * f)) := by 
  by_contra h
  simp at h




  
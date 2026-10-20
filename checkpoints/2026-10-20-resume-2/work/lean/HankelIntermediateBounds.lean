import HankelCoefficientBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Uniform actual Hankel bounds in the intermediate angular range -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.HankelIntermediateBounds

open OQ14.ModalAlgebra OQ14.HankelCoefficientBounds OQ14.HankelRealBasis

theorem leading_coefficient_zero : coefficient 0 0 = 1 := by
  norm_num [coefficient]

theorem leading_coefficient_succ (l : ℕ) :
    coefficient (l+1) (l+1) = (2*l+1 : ℕ)*coefficient l l := by
  have hf : (Nat.factorial (l+l+2) : ℝ) =
      (l+l+2 : ℕ)*(l+l+1 : ℕ)*(Nat.factorial (l+l) : ℝ) := by
    rw [Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  unfold coefficient
  rw [show l+1+(l+1)=l+l+2 by omega,hf,Nat.factorial_succ,pow_succ]
  simp only [Nat.sub_self,Nat.factorial_zero,Nat.cast_one,mul_one,Nat.cast_mul]
  push_cast
  field_simp
  ring

theorem leading_coefficient_bound (l : ℕ) : coefficient l l ≤ (2*l : ℝ)^l := by
  induction l with
  | zero => simp [leading_coefficient_zero]
  | succ l ih =>
    rw [leading_coefficient_succ]
    have hl : (2*l+1 : ℝ) ≤ 2*(l+1) := by linarith
    have hp : (2*l : ℝ)^l ≤ (2*(l+1) : ℝ)^l :=
      pow_le_pow_left₀ (by positivity) (by linarith) l
    have hmul := mul_le_mul hl (ih.trans hp) (coefficient_pos l l).le (by positivity : 0 ≤ 2*((l : ℝ)+1))
    convert hmul using 1 <;> push_cast <;> ring

def exponent (q : ℝ) : ℝ := 2+2*q*Real.log (4*q)

theorem scaled_leading_bound (l : ℕ) (q R r : ℝ) (hq : 1 ≤ q)
    (hR : 0 < R) (hRr : R ≤ r) (hl : (l : ℝ) ≤ 2*q*R) :
    coefficient l l/r^l ≤ Real.exp (2*q*R*Real.log (4*q)) := by
  have hr : 0 < r := lt_of_lt_of_le hR hRr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 2*(l : ℝ)/r ≤ 4*q := by
    apply (div_le_iff₀ hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hRr hqpos.le]
  have hlog : 0 ≤ Real.log (4*q) := Real.log_nonneg (by linarith)
  calc
    coefficient l l/r^l ≤ (2*l : ℝ)^l/r^l :=
      div_le_div_of_nonneg_right (leading_coefficient_bound l) (pow_pos hr l).le
    _ = (2*l/r : ℝ)^l := (div_pow _ _ _).symm
    _ ≤ (4*q)^l := pow_le_pow_left₀ (by positivity) hx l
    _ = Real.exp ((l : ℝ)*Real.log (4*q)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hl hlog)

theorem xi_intermediate_bound (l : ℕ) (q R r : ℝ) (hq : 1 ≤ q)
    (hR : 0 < R) (hRr : R ≤ r) (hrR : r ≤ 2*R) (hl : (l : ℝ) ≤ 2*q*R) :
    ‖xi l r‖ ≤ Real.exp (exponent q*R) := by
  have hr := lt_of_lt_of_le hR hRr
  calc
    _ ≤ (coefficient l l/r^l)*Real.exp r := xi_exponential_bound l r hr
    _ ≤ Real.exp (2*q*R*Real.log (4*q))*Real.exp (2*R) :=
      mul_le_mul (scaled_leading_bound l q R r hq hR hRr hl)
        (Real.exp_le_exp.mpr hrR) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add];congr 1;dsimp [exponent];ring

theorem xiD_intermediate_bound (l : ℕ) (q R r : ℝ) (hq : 1 ≤ q)
    (hR : 0 < R) (hRr : R ≤ r) (hrR : r ≤ 2*R) (hl : (l : ℝ) ≤ 2*q*R) :
    ‖xiD l r‖ ≤ (1+2*q)*Real.exp (exponent q*R) := by
  have hr := lt_of_lt_of_le hR hRr
  have hqr : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hc : 1+(l : ℝ)/r ≤ 1+2*q := by
    have hdiv : (l : ℝ)/r ≤ 2*q := (div_le_iff₀ hr).mpr
      (hl.trans (mul_le_mul_of_nonneg_left hRr (by positivity)))
    linarith
  have hbase : coefficient l l/r^l*Real.exp r ≤ Real.exp (exponent q*R) := by
    calc
      _ ≤ Real.exp (2*q*R*Real.log (4*q))*Real.exp (2*R) :=
        mul_le_mul (scaled_leading_bound l q R r hq hR hRr hl)
          (Real.exp_le_exp.mpr hrR) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;dsimp [exponent];ring
  exact (xiD_exponential_bound l r hr).trans (mul_le_mul hc hbase
    (mul_nonneg (div_nonneg (coefficient_pos l l).le (pow_pos hr l).le) (Real.exp_pos _).le)
    (by positivity))

end OQ14.HankelIntermediateBounds

#print axioms OQ14.HankelIntermediateBounds.leading_coefficient_zero
#print axioms OQ14.HankelIntermediateBounds.leading_coefficient_succ
#print axioms OQ14.HankelIntermediateBounds.leading_coefficient_bound
#print axioms OQ14.HankelIntermediateBounds.scaled_leading_bound
#print axioms OQ14.HankelIntermediateBounds.xi_intermediate_bound
#print axioms OQ14.HankelIntermediateBounds.xiD_intermediate_bound

import HankelRealBasis
import Mathlib.Algebra.BigOperators.Intervals

/-! # Actual reversed finite-Hankel coefficient and intermediate-order bounds -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.HankelCoefficientBounds

open Complex Finset OQ14.ModalAlgebra OQ14.ModalWronskian

def coefficient (l s : ℕ) : ℝ :=
  (Nat.factorial (l+s) : ℝ)/(2^s*(Nat.factorial s : ℝ)*(Nat.factorial (l-s) : ℝ))

theorem coefficient_pos (l s : ℕ) : 0 < coefficient l s := by
  unfold coefficient
  positivity

theorem coefficient_cast (l s : ℕ) : (coefficient l s : ℂ) = hankelCoeff l s 1 := by
  simp [coefficient,hankelCoeff]

theorem hankelCoeff_norm (l s : ℕ) (phase : ℂ) (hphase : ‖phase‖ = 1) :
    ‖hankelCoeff l s phase‖ = coefficient l s := by
  simp [hankelCoeff,coefficient,norm_div,norm_mul,norm_pow,hphase]

theorem coefficient_recurrence (l s : ℕ) (hs : s < l) :
    2*(s+1 : ℕ)*coefficient l (s+1) =
      (l+s+1 : ℕ)*(l-s : ℕ)*coefficient l s := by
  have h := hankelCoeff_recurrence l s 1 hs
  simp only [one_mul,←coefficient_cast] at h
  exact_mod_cast h

theorem coefficient_reverse_step (l s : ℕ) (hs : s < l) :
    (l-s : ℕ)*coefficient l s ≤ coefficient l (s+1) := by
  have h := coefficient_recurrence l s hs
  have hf : (2 : ℝ)*(s+1 : ℕ) ≤ (l+s+1 : ℕ) := by exact_mod_cast (by omega : 2*(s+1) ≤ l+s+1)
  have hn : 0 ≤ (l-s : ℕ)*coefficient l s := mul_nonneg (Nat.cast_nonneg _) (coefficient_pos l s).le
  have hm := mul_le_mul_of_nonneg_right hf hn
  have hpos : (0 : ℝ) < 2*(s+1 : ℕ) := by positivity
  nlinarith

theorem reversed_coefficient_factorial (l t : ℕ) (ht : t ≤ l) :
    (Nat.factorial t : ℝ)*coefficient l (l-t) ≤ coefficient l l := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htl : t ≤ l := by omega
    have hs : l-(t+1) < l := by omega
    have h := coefficient_reverse_step l (l-(t+1)) hs
    have he1 : l-(l-(t+1)) = t+1 := by omega
    have he2 : l-(t+1)+1 = l-t := by omega
    rw [he1,he2] at h
    have hh := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ Nat.factorial t)
    have hi := ih htl
    rw [Nat.factorial_succ,Nat.cast_mul]
    nlinarith

theorem reversed_coefficient_bound (l t : ℕ) (ht : t ≤ l) :
    coefficient l (l-t) ≤ coefficient l l/(Nat.factorial t : ℝ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < Nat.factorial t)).mpr
  simpa only [mul_comm] using reversed_coefficient_factorial l t ht

theorem hankelPoly_norm_sum (l : ℕ) (phase : ℂ) (hp : ‖phase‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    ‖hankelPoly l phase r‖ ≤ ∑ s ∈ range (l+1), coefficient l s/r^s := by
  unfold hankelPoly
  calc
    _ ≤ ∑ s ∈ range (l+1), ‖hankelCoeff l s phase*(r : ℂ)^(-(s : ℤ))‖ := norm_sum_le _ _
    _ = _ := by
      apply sum_congr rfl
      intro s _
      simp [norm_mul,hankelCoeff_norm l s phase hp,norm_zpow,Real.norm_eq_abs,
        abs_of_pos hr,zpow_neg,zpow_natCast,div_eq_mul_inv]

theorem reversed_term_bound (l t : ℕ) (ht : t ≤ l) (r : ℝ) (hr : 0 < r) :
    coefficient l (l-t)/r^(l-t) ≤ (coefficient l l/r^l)*(r^t/(Nat.factorial t : ℝ)) := by
  have h := div_le_div_of_nonneg_right (reversed_coefficient_bound l t ht)
    (le_of_lt (pow_pos hr (l-t)))
  have he : (coefficient l l/(Nat.factorial t : ℝ))/r^(l-t) =
      (coefficient l l/r^l)*(r^t/(Nat.factorial t : ℝ)) := by
    have he : r^l = r^(l-t)*r^t := by rw [←pow_add,Nat.sub_add_cancel ht]
    rw [he]
    field_simp
    ring
  exact h.trans_eq he

theorem hankelPoly_exponential_bound (l : ℕ) (phase : ℂ) (hp : ‖phase‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    ‖hankelPoly l phase r‖ ≤ coefficient l l/r^l*Real.exp r := by
  apply (hankelPoly_norm_sum l phase hp r hr).trans
  have hre : (∑ s ∈ range (l+1), coefficient l s/r^s) =
      ∑ t ∈ range (l+1), coefficient l (l-t)/r^(l-t) := by
    simpa only [Nat.add_sub_cancel] using
      (sum_range_reflect (fun s => coefficient l s/r^s) (l+1)).symm
  rw [hre]
  calc
    _ ≤ ∑ t ∈ range (l+1), (coefficient l l/r^l)*(r^t/(Nat.factorial t : ℝ)) := by
      apply sum_le_sum
      intro t ht
      exact reversed_term_bound l t (by have h := mem_range.mp ht;omega) r hr
    _ = (coefficient l l/r^l)*(∑ t ∈ range (l+1), r^t/(Nat.factorial t : ℝ)) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hr.le (l+1))
      (div_nonneg (coefficient_pos l l).le (pow_nonneg hr.le l))

theorem hankelPolyD_term_norm (l s : ℕ) (phase : ℂ) (hp : ‖phase‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    ‖hankelCoeff l s phase*((-(s : ℤ) : ℂ)*(r : ℂ)^(-(s : ℤ)-1))‖ =
      (s : ℝ)/r*(coefficient l s/r^s) := by
  rw [zpow_sub₀ (ofReal_ne_zero.mpr hr.ne')]
  simp [norm_mul,hankelCoeff_norm l s phase hp,norm_div,norm_zpow,
    Real.norm_eq_abs,abs_of_pos hr,zpow_neg,zpow_natCast,div_eq_mul_inv]
  ring

theorem hankelPolyD_norm_sum (l : ℕ) (phase : ℂ) (hp : ‖phase‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    ‖hankelPolyD l phase r‖ ≤ (l/r)*(∑ s ∈ range (l+1),coefficient l s/r^s) := by
  unfold hankelPolyD
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro s hs
  rw [hankelPolyD_term_norm l s phase hp r hr]
  have hsl : (s : ℝ) ≤ l := by exact_mod_cast (by have h := mem_range.mp hs;omega : s ≤ l)
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsl hr.le)
    (div_nonneg (coefficient_pos l s).le (pow_nonneg hr.le s))

theorem coefficient_sum_exponential_bound (l : ℕ) (r : ℝ) (hr : 0 < r) :
    (∑ s ∈ range (l+1),coefficient l s/r^s) ≤ coefficient l l/r^l*Real.exp r := by
  have h := hankelPoly_exponential_bound l 1 (by simp) r hr
  have he : ‖hankelPoly l 1 r‖ = ∑ s ∈ range (l+1),coefficient l s/r^s := by
    have hc : hankelPoly l 1 r = ((∑ s ∈ range (l+1),coefficient l s/r^s : ℝ) : ℂ) := by
      simp only [hankelPoly,ofReal_sum,ofReal_div,ofReal_pow,coefficient_cast]
      apply sum_congr rfl
      intro s _
      simp [div_eq_mul_inv]
    rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact sum_nonneg (fun s _ => div_nonneg (coefficient_pos l s).le (pow_nonneg hr.le s))
  rwa [he] at h

theorem hankelPolyD_exponential_bound (l : ℕ) (phase : ℂ) (hp : ‖phase‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    ‖hankelPolyD l phase r‖ ≤ (l/r)*(coefficient l l/r^l*Real.exp r) :=
  (hankelPolyD_norm_sum l phase hp r hr).trans
    (mul_le_mul_of_nonneg_left (coefficient_sum_exponential_bound l r hr) (by positivity))

theorem xi_exponential_bound (l : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖xi l r‖ ≤ coefficient l l/r^l*Real.exp r := by
  simpa [xi,norm_mul,norm_pow,Complex.norm_exp,p] using
    hankelPoly_exponential_bound l I (by simp) r hr

theorem xiD_exponential_bound (l : ℕ) (r : ℝ) (hr : 0 < r) :
    ‖xiD l r‖ ≤ (1+l/r)*(coefficient l l/r^l*Real.exp r) := by
  have hnorm : ‖xiD l r‖ = ‖I*p l r+pD l r‖ := by
    simp [xiD,norm_mul,norm_pow,Complex.norm_exp]
  rw [hnorm]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul]
  have h1 := hankelPoly_exponential_bound l I (by simp) r hr
  have h2 := hankelPolyD_exponential_bound l I (by simp) r hr
  exact (add_le_add h1 h2).trans_eq (by ring)

end OQ14.HankelCoefficientBounds

#print axioms OQ14.HankelCoefficientBounds.coefficient_pos
#print axioms OQ14.HankelCoefficientBounds.coefficient_cast
#print axioms OQ14.HankelCoefficientBounds.hankelCoeff_norm
#print axioms OQ14.HankelCoefficientBounds.coefficient_recurrence
#print axioms OQ14.HankelCoefficientBounds.coefficient_reverse_step
#print axioms OQ14.HankelCoefficientBounds.reversed_coefficient_factorial
#print axioms OQ14.HankelCoefficientBounds.reversed_coefficient_bound
#print axioms OQ14.HankelCoefficientBounds.hankelPoly_norm_sum
#print axioms OQ14.HankelCoefficientBounds.reversed_term_bound
#print axioms OQ14.HankelCoefficientBounds.hankelPoly_exponential_bound
#print axioms OQ14.HankelCoefficientBounds.hankelPolyD_term_norm
#print axioms OQ14.HankelCoefficientBounds.hankelPolyD_norm_sum
#print axioms OQ14.HankelCoefficientBounds.coefficient_sum_exponential_bound
#print axioms OQ14.HankelCoefficientBounds.hankelPolyD_exponential_bound
#print axioms OQ14.HankelCoefficientBounds.xi_exponential_bound
#print axioms OQ14.HankelCoefficientBounds.xiD_exponential_bound

import Packet06PhysicalPairLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06AnnularLowerBound
open MeasureTheory

theorem lower (w : ℝ → ℝ) (hw : Continuous w) (hc : HasCompactSupport w)
    (hnonneg : ∀ r, 0 ≤ w r) (f : ℝ → ℂ) (hf : Continuous f) (A : ℂ)
    (hclose : ∀ r, w r ≠ 0 → ‖f r-A‖ ≤ ‖A‖/2) :
    (‖A‖/2)*(∫ r, w r) ≤ ‖∫ r, (w r : ℂ)*f r‖ := by
  have hwi : Integrable w := hw.integrable_of_hasCompactSupport hc
  have hprod : Integrable (fun r => (w r : ℂ)*f r) :=
    ((Complex.continuous_ofReal.comp hw).mul hf).integrable_of_hasCompactSupport (hc.comp_left (g := Complex.ofReal) (by simp) |>.mul_right)
  have hconst : Integrable (fun r => (w r : ℂ)*A) := hwi.ofReal.mul_const A
  have hdiff : ‖(∫ r, (w r : ℂ)*f r) - (∫ r, (w r : ℂ)*A)‖ ≤
      (‖A‖/2)*(∫ r, w r) := by
    rw [← integral_sub hprod hconst, ← integral_const_mul]
    apply norm_integral_le_of_norm_le (hwi.const_mul (‖A‖/2))
    filter_upwards with r
    by_cases hz : w r = 0
    · simp [hz]
    · have hh := hclose r hz
      have he : (w r : ℂ)*f r-(w r : ℂ)*A = (w r : ℂ)*(f r-A) := by ring
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnonneg r)]
      nlinarith [mul_le_mul_of_nonneg_left hh (hnonneg r)]
  have hI : 0 ≤ ∫ r, w r := integral_nonneg hnonneg
  have he : (∫ r, (w r : ℂ)*A) = (∫ r, w r : ℝ)*A := by
    rw [integral_mul_const]
    congr 1
    exact integral_ofReal
  rw [he] at hdiff
  have htri := norm_le_norm_add_norm_sub (∫ r, (w r : ℂ)*f r) ((∫ r, w r : ℝ)*A)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hI] at htri
  nlinarith
theorem relative_weight (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ)
    (R : ℝ) (hs : tsupport ζ ⊆ Set.Ioo (0 : ℝ) R) (_hR : 0 ≤ R) (α : ℝ) (hα : 0 ≤ α) :
    (∫ r in Set.Ioi (0 : ℝ), r^(2+α)*|ζ r|) ≤
      R^α * ∫ r in Set.Ioi (0 : ℝ), r^2*|ζ r| := by
  have hi1 : IntegrableOn (fun r : ℝ => r^(2+α)*|ζ r|) (Set.Ioi (0 : ℝ)) := by
    have hh : Continuous (fun r : ℝ => r^(2+α)*|ζ r|) :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ 2+α)).mul hζ.abs
    exact (hh.integrable_of_hasCompactSupport (hc.norm.mul_left)).integrableOn
  have hi2 : IntegrableOn (fun r : ℝ => r^2*|ζ r|) (Set.Ioi (0 : ℝ)) :=
    (((continuous_id.pow 2).mul hζ.abs).integrable_of_hasCompactSupport (hc.norm.mul_left)).integrableOn
  rw [← integral_const_mul]
  apply integral_mono_ae hi1 (hi2.const_mul (R^α))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  by_cases hz : ζ r = 0
  · simp [hz]
  · have hrR : r ≤ R := (hs (subset_tsupport ζ hz)).2.le
    have hp := Real.rpow_le_rpow hr.le hrR hα
    have hpow : r^(2+α) = r^2*r^α := by
      rw [Real.rpow_add hr,Real.rpow_two]
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg r) (abs_nonneg (ζ r)))]
#print axioms OQ14.Packet06AnnularLowerBound.lower
#print axioms OQ14.Packet06AnnularLowerBound.relative_weight
end OQ14.Packet06AnnularLowerBound

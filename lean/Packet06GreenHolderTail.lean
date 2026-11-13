import KernelEstimates
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderTail
open MeasureTheory Set Metric OQ14.Maxwell OQ14.KernelEstimates

theorem inverse_fourth_tail (a : ℝ) (ha : 0 < a) :
    (∫ x : Space in {x | a < ‖x‖}, (‖x‖⁻¹)^4) =
      3 * (volume : Measure Space).real (ball 0 1) / a := by
  classical
  have h := radial_integral (fun r => if a < r then (r⁻¹)^4 else 0)
  have hs : MeasurableSet {x : Space | a < ‖x‖} := measurableSet_lt measurable_const continuous_norm.measurable
  have he : (fun x : Space => if a < ‖x‖ then (‖x‖⁻¹)^4 else 0) =
      {x : Space | a < ‖x‖}.indicator (fun x => (‖x‖⁻¹)^4) := by
    funext x
    simp [Set.indicator_apply]
  rw [he, integral_indicator hs] at h
  have hi : (∫ r in Ioi (0 : ℝ), r^2 * (if a < r then (r⁻¹)^4 else 0)) =
      ∫ r in Ioi a, r ^ (-2 : ℝ) := by
    have hh : (∫ r in Ioi (0 : ℝ), r^2 * (if a < r then (r⁻¹)^4 else 0)) =
        ∫ r in Ioi (0 : ℝ), (Ioi a).indicator (fun t => t ^ (-2 : ℝ)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      by_cases har : a < r
      · have hr0 : r ≠ 0 := ne_of_gt hr
        simp only [har, if_true, Set.indicator_of_mem, mem_Ioi]
        rw [Real.rpow_neg (le_of_lt hr)]
        field_simp
        ring
      · simp [har]
    rw [hh, setIntegral_indicator measurableSet_Ioi]
    rw [inter_eq_right.mpr (Ioi_subset_Ioi (le_of_lt ha))]
  rw [hi, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha] at h
  norm_num at h
  simpa [Real.rpow_neg (le_of_lt ha), div_eq_mul_inv, mul_assoc] using h

/-- The same inverse-fourth tail is genuinely integrable, not merely a formal integral. -/
theorem inverse_fourth_tail_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : Space => (‖x‖⁻¹)^4) {x | a < ‖x‖} := by
  apply Integrable.of_integral_ne_zero
  rw [inverse_fourth_tail a ha]
  have hv : 0 < (volume : Measure Space).real (ball 0 1) := by
    apply ENNReal.toReal_pos (measure_ball_pos volume (0 : Space) zero_lt_one).ne'
    exact measure_ball_lt_top.ne
  positivity
#print axioms OQ14.Packet06GreenHolderTail.inverse_fourth_tail
#print axioms OQ14.Packet06GreenHolderTail.inverse_fourth_tail_integrable
end OQ14.Packet06GreenHolderTail

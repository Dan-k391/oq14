import Packet06GreenHolderTail
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderTranslatedMass
open MeasureTheory Set Metric OQ14.Maxwell OQ14.KernelEstimates

theorem inverse_sq_translated_ball (x : Space) (r : ℝ) (hr : 0 ≤ r) :
    (∫ y : Space in {y | ‖x-y‖ ≤ r}, (‖x-y‖⁻¹)^2) =
      3 * (volume : Measure Space).real (ball 0 1) * r := by
  have hm := (Measure.measurePreserving_sub_left (volume : Measure Space) x).integral_comp
    (MeasurableEquiv.subLeft x).measurableEmbedding
    ((closedBall (0 : Space) r).indicator (fun y => (‖y‖⁻¹)^2))
  rw [integral_indicator measurableSet_closedBall] at hm
  rw [← inverse_norm_sq_integral_ball r hr, ← hm, ← integral_indicator]
  · apply integral_congr_ae
    filter_upwards with y
    by_cases hy : ‖x-y‖ ≤ r
    · simp [hy, mem_closedBall, dist_zero_right]
    · simp [hy, mem_closedBall, dist_zero_right]
  · exact measurableSet_le (continuous_norm.comp (continuous_const.sub continuous_id)).measurable measurable_const

theorem inverse_fourth_translated_tail (x : Space) (r : ℝ) (hr : 0 < r) :
    (∫ y : Space in {y | r < ‖x-y‖}, (‖x-y‖⁻¹)^4) =
      3 * (volume : Measure Space).real (ball 0 1) / r := by
  have hm := (Measure.measurePreserving_sub_left (volume : Measure Space) x).integral_comp
    (MeasurableEquiv.subLeft x).measurableEmbedding
    ({y : Space | r < ‖y‖}.indicator (fun y => (‖y‖⁻¹)^4))
  have hs : MeasurableSet {y : Space | r < ‖y‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [integral_indicator hs] at hm
  rw [← OQ14.Packet06GreenHolderTail.inverse_fourth_tail r hr, ← hm, ← integral_indicator]
  · apply integral_congr_ae
    filter_upwards with y
    by_cases hy : r < ‖x-y‖
    · simp [hy]
    · simp [hy]
  · exact measurableSet_lt measurable_const (continuous_norm.comp (continuous_const.sub continuous_id)).measurable
theorem inverse_fourth_translated_tail_integrable (x : Space) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun y : Space => (‖x-y‖⁻¹)^4) {y | r < ‖x-y‖} := by
  apply Integrable.of_integral_ne_zero
  rw [inverse_fourth_translated_tail x r hr]
  have hv : 0 < (volume : Measure Space).real (ball 0 1) := by
    apply ENNReal.toReal_pos (measure_ball_pos volume (0 : Space) zero_lt_one).ne'
    exact measure_ball_lt_top.ne
  positivity
theorem inverse_sq_translated_ball_integrable (x : Space) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun y : Space => (‖x-y‖⁻¹)^2) {y | ‖x-y‖ ≤ r} := by
  apply Integrable.of_integral_ne_zero
  rw [inverse_sq_translated_ball x r (le_of_lt hr)]
  have hv : 0 < (volume : Measure Space).real (ball 0 1) := by
    apply ENNReal.toReal_pos (measure_ball_pos volume (0 : Space) zero_lt_one).ne'
    exact measure_ball_lt_top.ne
  positivity
/-- The squared Coulomb gradient majorant has linear mass in the displacement. -/
theorem squared_far_majorant_mass (x : Space) (h : ℝ) (hh : 0 < h) :
    (∫ y : Space in {y | h < ‖x-y‖},
      (2*h * (‖x-y‖⁻¹)^2)^2) =
      4*h * (3 * (volume : Measure Space).real (ball 0 1)) := by
  have he : (fun y : Space => (2*h * (‖x-y‖⁻¹)^2)^2) =
      (fun y => (4*h^2) * (‖x-y‖⁻¹)^4) := by
    funext y
    ring
  rw [he, integral_const_mul, inverse_fourth_translated_tail x h hh]
  field_simp
  ring
#print axioms OQ14.Packet06GreenHolderTranslatedMass.squared_far_majorant_mass
#print axioms OQ14.Packet06GreenHolderTranslatedMass.inverse_sq_translated_ball_integrable
#print axioms OQ14.Packet06GreenHolderTranslatedMass.inverse_fourth_translated_tail_integrable
#print axioms OQ14.Packet06GreenHolderTranslatedMass.inverse_sq_translated_ball
#print axioms OQ14.Packet06GreenHolderTranslatedMass.inverse_fourth_translated_tail
end OQ14.Packet06GreenHolderTranslatedMass

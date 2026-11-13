import Packet06GreenHolderTranslatedMass
import Packet06GreenHolderPointwise
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderFar
open MeasureTheory Set Metric OQ14.Maxwell OQ14.Packet06GreenHolderPointwise
open OQ14.Packet06GreenHolderTranslatedMass

theorem coulomb_far_pointwise (x x' y : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) (hy : 2*h < ‖x-y‖) :
    |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2 ≤ (2*h * (‖x-y‖⁻¹)^2)^2 := by
  have hd' : (x-y)-(x'-y) = x-x' := by abel
  have hu : x-y ≠ 0 := by
    intro he
    rw [he, norm_zero] at hy
    linarith
  have hfar : 2*‖(x-y)-(x'-y)‖ ≤ ‖x-y‖ := by rw [hd',hd]; linarith
  have hb := inverse_norm_difference_far (x-y) (x'-y) hfar hu
  rw [hd', hd] at hb
  have heq : 2*h / ‖x-y‖^2 = 2*h*(‖x-y‖⁻¹)^2 := by rw [div_eq_mul_inv, inv_pow]
  rw [heq] at hb
  nlinarith [abs_nonneg (‖x-y‖⁻¹ - ‖x'-y‖⁻¹)]

theorem coulomb_far_integral (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    (∫ y : Space in {y | 2*h < ‖x-y‖},
      |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) ≤
      4*h * (3 * (volume : Measure Space).real (ball 0 1)) := by
  let A : Set Space := {y | 2*h < ‖x-y‖}
  let g : Space → ℝ := fun y => (2*h * (‖x-y‖⁻¹)^2)^2
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable
  have hgi : IntegrableOn g A := by
    have hi := inverse_fourth_translated_tail_integrable x (2*h) (by positivity)
    have hi' := hi.const_mul (4*h^2)
    apply hi'.congr
    filter_upwards with y
    dsimp [g]
    ring
  have hfm : AEStronglyMeasurable (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      (volume.restrict A) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hfi : IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) A := by
    apply hgi.mono' hfm
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact coulomb_far_pointwise x x' y h hh hd hy
  have hle := integral_mono_ae hfi hgi (by
    filter_upwards [ae_restrict_mem hA] with y hy
    exact coulomb_far_pointwise x x' y h hh hd hy)
  have hm := squared_far_majorant_mass x (2*h) (by positivity)
  have he : (∫ y : Space in A, g y) ≤
      4*h * (3 * (volume : Measure Space).real (ball 0 1)) := by
    have hm' : (∫ y : Space in A, g y) =
        (1/4 : ℝ) * (∫ y : Space in A, (2*(2*h) * (‖x-y‖⁻¹)^2)^2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [g]
      ring
    rw [hm', hm]
    have hv : 0 ≤ (volume : Measure Space).real (ball 0 1) := measureReal_nonneg
    nlinarith
  exact hle.trans he
theorem coulomb_far_integrable (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      {y | 2*h < ‖x-y‖} := by
  let A : Set Space := {y | 2*h < ‖x-y‖}
  let g : Space → ℝ := fun y => (2*h * (‖x-y‖⁻¹)^2)^2
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable
  have hgi : IntegrableOn g A := by
    have hi := inverse_fourth_translated_tail_integrable x (2*h) (by positivity)
    have hi' := hi.const_mul (4*h^2)
    apply hi'.congr
    filter_upwards with y
    dsimp [g]
    ring
  have hfm : AEStronglyMeasurable (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      (volume.restrict A) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hfi : IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) A := by
    apply hgi.mono' hfm
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact coulomb_far_pointwise x x' y h hh hd hy
  exact hfi

#print axioms OQ14.Packet06GreenHolderFar.coulomb_far_integrable
#print axioms OQ14.Packet06GreenHolderFar.coulomb_far_integral
#print axioms OQ14.Packet06GreenHolderFar.coulomb_far_pointwise
end OQ14.Packet06GreenHolderFar

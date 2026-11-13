import Packet06GreenHolderFar
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderNear
open MeasureTheory Set Metric OQ14.Maxwell OQ14.Packet06GreenHolderTranslatedMass

theorem coulomb_near_integral (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    (∫ y : Space in {y | ‖x-y‖ ≤ 2*h},
      |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) ≤
      10*h * (3 * (volume : Measure Space).real (ball 0 1)) := by
  let A : Set Space := {y | ‖x-y‖ ≤ 2*h}
  let B : Set Space := {y | ‖x'-y‖ ≤ 3*h}
  let f : Space → ℝ := fun y => (‖x-y‖⁻¹)^2
  let g : Space → ℝ := fun y => (‖x'-y‖⁻¹)^2
  have hAB : A ⊆ B := by
    intro y hy
    change ‖x'-y‖ ≤ 3*h
    have he : x'-y = (x'-x)+(x-y) := by abel
    rw [he]
    have ht := norm_add_le (x'-x) (x-y)
    rw [norm_sub_rev, hd] at ht
    change ‖x-y‖ ≤ 2*h at hy
    linarith
  have hA : MeasurableSet A := measurableSet_le
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable measurable_const
  have hfi : IntegrableOn f A := inverse_sq_translated_ball_integrable x (2*h) (by positivity)
  have hgiB : IntegrableOn g B := inverse_sq_translated_ball_integrable x' (3*h) (by positivity)
  have hgi : IntegrableOn g A := hgiB.mono_set hAB
  have hmajor : IntegrableOn (fun y => 2*f y + 2*g y) A :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hfm : AEStronglyMeasurable (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      (volume.restrict A) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : ∀ y : Space, |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2 ≤ 2*f y + 2*g y := by
    intro y
    rw [sq_abs]
    dsimp [f,g]
    nlinarith [sq_nonneg (‖x-y‖⁻¹ + ‖x'-y‖⁻¹)]
  have hactual : IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) A := by
    apply hmajor.mono' hfm
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound y
  have hi := integral_mono_ae hactual hmajor (by filter_upwards with y; exact hbound y)
  rw [integral_add (hfi.const_mul 2) (hgi.const_mul 2), integral_const_mul, integral_const_mul] at hi
  have hf := inverse_sq_translated_ball x (2*h) (by positivity)
  have hg := inverse_sq_translated_ball x' (3*h) (by positivity)
  have hgm : (∫ y : Space in A, g y) ≤ ∫ y : Space in B, g y := by
    apply setIntegral_mono_set hgiB
    · filter_upwards with y
      exact sq_nonneg _
    · exact Filter.Eventually.of_forall hAB
  change (∫ y : Space in A, f y) = _ at hf
  change (∫ y : Space in B, g y) = _ at hg
  rw [hf] at hi
  rw [hg] at hgm
  nlinarith

theorem coulomb_near_integrable (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      {y | ‖x-y‖ ≤ 2*h} := by
  let A : Set Space := {y | ‖x-y‖ ≤ 2*h}
  let B : Set Space := {y | ‖x'-y‖ ≤ 3*h}
  let f : Space → ℝ := fun y => (‖x-y‖⁻¹)^2
  let g : Space → ℝ := fun y => (‖x'-y‖⁻¹)^2
  have hAB : A ⊆ B := by
    intro y hy
    change ‖x'-y‖ ≤ 3*h
    have he : x'-y = (x'-x)+(x-y) := by abel
    rw [he]
    have ht := norm_add_le (x'-x) (x-y)
    rw [norm_sub_rev, hd] at ht
    change ‖x-y‖ ≤ 2*h at hy
    linarith
  have hA : MeasurableSet A := measurableSet_le
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable measurable_const
  have hfi : IntegrableOn f A := inverse_sq_translated_ball_integrable x (2*h) (by positivity)
  have hgiB : IntegrableOn g B := inverse_sq_translated_ball_integrable x' (3*h) (by positivity)
  have hgi : IntegrableOn g A := hgiB.mono_set hAB
  have hmajor : IntegrableOn (fun y => 2*f y + 2*g y) A :=
    (hfi.const_mul 2).add (hgi.const_mul 2)
  have hfm : AEStronglyMeasurable (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2)
      (volume.restrict A) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hbound : ∀ y : Space, |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2 ≤ 2*f y + 2*g y := by
    intro y
    rw [sq_abs]
    dsimp [f,g]
    nlinarith [sq_nonneg (‖x-y‖⁻¹ + ‖x'-y‖⁻¹)]
  have hactual : IntegrableOn (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) A := by
    apply hmajor.mono' hfm
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound y
  exact hactual

#print axioms OQ14.Packet06GreenHolderNear.coulomb_near_integrable
#print axioms OQ14.Packet06GreenHolderNear.coulomb_near_integral
end OQ14.Packet06GreenHolderNear

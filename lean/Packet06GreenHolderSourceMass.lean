import Packet06GreenHolderKernel
import Packet06GreenHolderNear
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderSourceMass
open MeasureTheory Set Metric OQ14.Maxwell OQ14.Packet06GreenHolderTranslatedMass

theorem inverse_sq_source_integral (x : Space) (R S : ℝ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hx : ‖x‖ ≤ R) :
    (∫ y : Space in closedBall 0 S, (‖x-y‖⁻¹)^2) ≤
      3 * (volume : Measure Space).real (ball 0 1) * (R+S+1) := by
  let A : Set Space := closedBall 0 S
  let B : Set Space := {y | ‖x-y‖ ≤ R+S+1}
  have hAB : A ⊆ B := by
    intro y hy
    change ‖x-y‖ ≤ R+S+1
    change y ∈ closedBall (0 : Space) S at hy
    have hy' : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hy
    have ht := norm_sub_le x y
    linarith
  have hb : 0 < R+S+1 := by linarith
  have hi := inverse_sq_translated_ball_integrable x (R+S+1) hb
  have h := setIntegral_mono_set hi (by filter_upwards with y; exact sq_nonneg _) (Filter.Eventually.of_forall hAB)
  rw [inverse_sq_translated_ball x (R+S+1) (le_of_lt hb)] at h
  exact h

/-- The Coulomb singularity cancels: its squared difference has globally linear mass. -/
theorem coulomb_global_integral (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    (∫ y : Space, |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) ≤
      14*h * (3 * (volume : Measure Space).real (ball 0 1)) := by
  let A : Set Space := {y | ‖x-y‖ ≤ 2*h}
  let f : Space → ℝ := fun y => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2
  have hA : MeasurableSet A := measurableSet_le
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable measurable_const
  have hc : Aᶜ = {y : Space | 2*h < ‖x-y‖} := by ext y; simp [A, not_le]
  have hiA : IntegrableOn f A := OQ14.Packet06GreenHolderNear.coulomb_near_integrable x x' h hh hd
  have hiC : IntegrableOn f Aᶜ := by
    rw [hc]
    exact OQ14.Packet06GreenHolderFar.coulomb_far_integrable x x' h hh hd
  have hi : Integrable f := by
    have hu := hiA.union hiC
    simpa only [union_compl_self, integrableOn_univ] using hu
  have hn := OQ14.Packet06GreenHolderNear.coulomb_near_integral x x' h hh hd
  have hf := OQ14.Packet06GreenHolderFar.coulomb_far_integral x x' h hh hd
  change (∫ y in A, f y) ≤ _ at hn
  rw [← hc] at hf
  change (∫ y in Aᶜ, f y) ≤ _ at hf
  rw [← integral_add_compl hA hi]
  linarith
theorem coulomb_global_integrable (x x' : Space) (h : ℝ) (hh : 0 < h)
    (hd : ‖x-x'‖ = h) :
    Integrable (fun y : Space => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2) := by
  let A : Set Space := {y | ‖x-y‖ ≤ 2*h}
  let f : Space → ℝ := fun y => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2
  have hA : MeasurableSet A := measurableSet_le
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable measurable_const
  have hc : Aᶜ = {y : Space | 2*h < ‖x-y‖} := by ext y; simp [A, not_le]
  have hiA : IntegrableOn f A := OQ14.Packet06GreenHolderNear.coulomb_near_integrable x x' h hh hd
  have hiC : IntegrableOn f Aᶜ := by
    rw [hc]
    exact OQ14.Packet06GreenHolderFar.coulomb_far_integrable x x' h hh hd
  have hi : Integrable f := by
    have hu := hiA.union hiC
    simpa only [union_compl_self, integrableOn_univ] using hu
  exact hi

#print axioms OQ14.Packet06GreenHolderSourceMass.coulomb_global_integrable
#print axioms OQ14.Packet06GreenHolderSourceMass.coulomb_global_integral
#print axioms OQ14.Packet06GreenHolderSourceMass.inverse_sq_source_integral
end OQ14.Packet06GreenHolderSourceMass

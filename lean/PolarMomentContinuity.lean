import PolarMomentTesting

/-! Actual continuity and uniform bounds of bounded-angular moments. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.PolarMomentContinuity
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.PolarMomentTesting
open scoped Topology

theorem moment_continuous (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hb : ∀ n, ‖σ n‖ ≤ C) :
    Continuous (moment f σ) := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf
  apply continuous_of_dominated (bound := fun _ : Sphere => M*C)
  · intro r
    exact ((hf.comp (continuous_const.smul continuous_subtype_val)).measurable.mul hσ).aestronglyMeasurable
  · intro r
    exact Filter.Eventually.of_forall (fun n => by
      rw [norm_mul]
      exact mul_le_mul (hM _) (hb n) (norm_nonneg _) (le_trans (norm_nonneg (f 0)) (hM 0)))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun n => (hf.comp (continuous_id.smul continuous_const)).mul continuous_const)

theorem moment_norm_le (f : Space → ℂ) (σ : Sphere → ℂ) (M C : ℝ)
    (hM : 0 ≤ M) (hb : ∀ n, ‖σ n‖ ≤ C) (r : ℝ) (hf : ∀ n : Sphere, ‖f (r • (n : Space))‖ ≤ M) :
    ‖moment f σ r‖ ≤ M*C*(angularMeasure Set.univ).toReal := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with n
  exact (norm_mul _ _).trans_le (mul_le_mul (hf n) (hb n) (norm_nonneg _) hM)

end OQ14.PolarMomentContinuity

#print axioms OQ14.PolarMomentContinuity.moment_continuous
#print axioms OQ14.PolarMomentContinuity.moment_norm_le

import PolarMomentAE

/-! Literal angular moments of a spatially essentially bounded field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.PolarMomentBound
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.PolarMomentTesting

theorem moment_bound_ae (f : Space → ℂ) (R M C : ℝ) (hM : 0 ≤ M) (σ : Sphere → ℂ)
    (hσ : ∀ n, ‖σ n‖ ≤ C)
    (hf : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖f x‖ ≤ M) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖moment f σ r‖ ≤ M*C*(angularMeasure univ).toReal := by
  have hp := PolarMomentAE.polar_ae (ae_imp_of_ae_restrict hf)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hp,ae_restrict_mem measurableSet_Ioo] with r hr hm
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hr] with n hn
  have hx : r • (n : Space) ∈ ball (0 : Space) R := by
    simpa only [mem_ball,dist_zero_right,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos hm.1,mul_one] using hm.2
  exact (norm_mul _ _).trans_le (mul_le_mul (hn hx) (hσ n) (norm_nonneg _) hM)

end OQ14.PolarMomentBound

#print axioms OQ14.PolarMomentBound.moment_bound_ae

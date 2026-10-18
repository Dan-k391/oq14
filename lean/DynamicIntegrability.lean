import KernelIntegrability

/-! # Actual local L1 and L2 estimates for the dynamic Maxwell remainder -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.DynamicIntegrability

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel OQ14.DyadicKernel
  OQ14.KernelIntegrability Metric

theorem remainder_measurable (k : ℝ) (i j : Fin 3) :
    Measurable (fun x : Space => remainder k x i j) := by
  unfold remainder dyadic phi phiHessian radialDD radialD radial
  fun_prop

theorem remainder_zero (k : ℝ) (i j : Fin 3) : remainder k 0 i j = 0 := by
  simp [remainder, dyadic, phi, phiHessian, radialDD, radialD, radial]

theorem remainder_bound_all (k : ℝ) (x : Space) (hsmall : |k| * ‖x‖ ≤ 1)
    (i j : Fin 3) : ‖remainder k x i j‖ ≤ (14 * k^2 / (4 * Real.pi)) * ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [remainder_zero]
  · simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using
      remainder_bound k x hx hsmall i j

theorem remainder_integrable_ball (k R : ℝ) (hsmall : |k| * R ≤ 1) (i j : Fin 3) :
    IntegrableOn (fun x : Space => remainder k x i j) (closedBall 0 R) := by
  apply ((inverse_norm_integrable_ball R).const_mul (14 * k^2 / (4 * Real.pi))).mono'
    (remainder_measurable k i j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  have hnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  exact remainder_bound_all k x ((mul_le_mul_of_nonneg_left hnorm (abs_nonneg k)).trans hsmall) i j

theorem remainder_memLp_two_ball (k R : ℝ) (hsmall : |k| * R ≤ 1) (i j : Fin 3) :
    MemLp (fun x : Space => remainder k x i j) 2 (volume.restrict (closedBall 0 R)) := by
  have hm : Measurable (fun x : Space => ‖x‖⁻¹) := continuous_norm.measurable.inv
  have hi : MemLp (fun x : Space => ‖x‖⁻¹) 2 (volume.restrict (closedBall 0 R)) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using inverse_norm_sq_integrable_ball R
  apply hi.of_le_mul (remainder_measurable k i j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  have hnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  simpa only [Real.norm_eq_abs, abs_inv, abs_norm] using
    remainder_bound_all k x ((mul_le_mul_of_nonneg_left hnorm (abs_nonneg k)).trans hsmall) i j

end OQ14.DynamicIntegrability

#print axioms OQ14.DynamicIntegrability.remainder_measurable
#print axioms OQ14.DynamicIntegrability.remainder_zero
#print axioms OQ14.DynamicIntegrability.remainder_bound_all
#print axioms OQ14.DynamicIntegrability.remainder_integrable_ball
#print axioms OQ14.DynamicIntegrability.remainder_memLp_two_ball

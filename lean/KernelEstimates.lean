import DynamicIntegrability

/-! # Exact radial mass of the three-dimensional singular kernels -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.KernelEstimates

open MeasureTheory Set Metric OQ14.Maxwell OQ14.KernelIntegrability

theorem radial_integral (f : ℝ → ℝ) :
    (∫ x : Space, f ‖x‖) =
      3 * (volume : Measure Space).real (ball 0 1) * ∫ r in Ioi (0 : ℝ), r^2 * f r := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using
    integral_fun_norm_addHaar (volume : Measure Space) f

theorem inverse_norm_integral_ball (R : ℝ) (hR : 0 ≤ R) :
    (∫ x : Space in closedBall 0 R, ‖x‖⁻¹) =
      (3 / 2 : ℝ) * (volume : Measure Space).real (ball 0 1) * R^2 := by
  classical
  have h := radial_integral (fun r => if r ≤ R then r⁻¹ else 0)
  have he : (fun x : Space => if ‖x‖ ≤ R then ‖x‖⁻¹ else 0) =
      (closedBall 0 R).indicator (fun x => ‖x‖⁻¹) := by
    funext x
    simp [Set.indicator_apply, mem_closedBall, dist_zero_right]
  rw [he, integral_indicator measurableSet_closedBall] at h
  have hi : (∫ r in Ioi (0 : ℝ), r^2 * (if r ≤ R then r⁻¹ else 0)) =
      ∫ r in Ioc (0 : ℝ) R, r := by
    have hh : (∫ r in Ioi (0 : ℝ), r^2 * (if r ≤ R then r⁻¹ else 0)) =
        ∫ r in Ioi (0 : ℝ), (Iic R).indicator (fun t => t) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : r ≠ 0 := ne_of_gt hr
      by_cases hle : r ≤ R
      · simp [hle, hr0, pow_two]
      · simp [hle]
    rw [hh, setIntegral_indicator measurableSet_Iic]
    rfl
  rw [hi] at h
  rw [← intervalIntegral.integral_of_le hR, integral_id] at h
  convert h using 1
  ring

theorem inverse_norm_sq_integral_ball (R : ℝ) (hR : 0 ≤ R) :
    (∫ x : Space in closedBall 0 R, (‖x‖⁻¹)^2) =
      3 * (volume : Measure Space).real (ball 0 1) * R := by
  classical
  have h := radial_integral (fun r => if r ≤ R then (r⁻¹)^2 else 0)
  have he : (fun x : Space => if ‖x‖ ≤ R then (‖x‖⁻¹)^2 else 0) =
      (closedBall 0 R).indicator (fun x => (‖x‖⁻¹)^2) := by
    funext x
    simp [Set.indicator_apply, mem_closedBall, dist_zero_right]
  rw [he, integral_indicator measurableSet_closedBall] at h
  have hi : (∫ r in Ioi (0 : ℝ), r^2 * (if r ≤ R then (r⁻¹)^2 else 0)) =
      ∫ r in Ioc (0 : ℝ) R, (1 : ℝ) := by
    have hh : (∫ r in Ioi (0 : ℝ), r^2 * (if r ≤ R then (r⁻¹)^2 else 0)) =
        ∫ r in Ioi (0 : ℝ), (Iic R).indicator (fun _ => (1 : ℝ)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : r ≠ 0 := ne_of_gt hr
      by_cases hle : r ≤ R
      · simp [hle, hr0, ← mul_pow]
      · simp [hle]
    rw [hh, setIntegral_indicator measurableSet_Iic]
    rfl
  rw [hi] at h
  rw [← intervalIntegral.integral_of_le hR] at h
  simpa using h

/-- The actual dynamic dyadic remainder has a quadratic local L1 mass bound. -/
theorem remainder_integral_norm_bound (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : |k| * R ≤ 1) (i j : Fin 3) :
    (∫ x : Space in closedBall 0 R, ‖OQ14.DyadicKernel.remainder k x i j‖) ≤
      (14 * k^2 / (4 * Real.pi)) *
        ((3 / 2 : ℝ) * (volume : Measure Space).real (ball 0 1) * R^2) := by
  have h := integral_mono_ae
    (OQ14.DynamicIntegrability.remainder_integrable_ball k R hsmall i j).norm
    ((inverse_norm_integrable_ball R).const_mul (14 * k^2 / (4 * Real.pi)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
      exact OQ14.DynamicIntegrability.remainder_bound_all k x
        ((mul_le_mul_of_nonneg_left hn (abs_nonneg k)).trans hsmall) i j)
  rw [integral_const_mul, inverse_norm_integral_ball R hR] at h
  exact h

end OQ14.KernelEstimates

#print axioms OQ14.KernelEstimates.radial_integral
#print axioms OQ14.KernelEstimates.inverse_norm_integral_ball
#print axioms OQ14.KernelEstimates.inverse_norm_sq_integral_ball
#print axioms OQ14.KernelEstimates.remainder_integral_norm_bound

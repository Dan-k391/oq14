import RealKernelBounds
import PointSingularity

/-! # Actual local gradient and first weak derivative of the outgoing kernel -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.KernelGradient

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel Metric

theorem gradient_measurable (k : ℝ) (j : Fin 3) :
    Measurable (fun x : Space => phiGradient k x j) := by
  unfold phiGradient radialD
  fun_prop

theorem gradient_differentiableAt (k : ℝ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y => phiGradient k y j) x := by
  have hd := radialD_hasDerivAt k ‖x‖ (norm_ne_zero_iff.mpr hx)
  have hr := (hd.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  have hu := unitCoordinate_differentiableAt j x hx
  have he : (fun y => phiGradient k y j) =
      fun y => (1 / (4 * Real.pi) : ℂ) * (radialD k ‖y‖ * unitCoordinate j y) := by
    funext y
    simp [phiGradient, unitCoordinate, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [he]
  exact (hr.mul hu).const_mul _

theorem gradient_bound (k : ℝ) (x : Space) (j : Fin 3) :
    ‖phiGradient k x j‖ ≤ (4 * Real.pi)⁻¹ * (|k| * ‖x‖⁻¹ + (‖x‖⁻¹)^2) := by
  by_cases hx : x = 0
  · subst x
    simp [phiGradient, radialD]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖((x j / ‖x‖ : ℝ) : ℂ)‖ ≤ 1 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm]
    exact (div_le_one hr).mpr (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
  have hd : ‖radialD k ‖x‖‖ ≤ |k| * ‖x‖⁻¹ + (‖x‖⁻¹)^2 := by
    unfold radialD
    rw [norm_mul, show ‖Complex.exp (Complex.I * k * ‖x‖)‖ = 1 by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im], one_mul]
    have h := norm_sub_le (Complex.I * k / (‖x‖ : ℂ)) (1 / (‖x‖ : ℂ)^2)
    simpa only [norm_div, norm_mul, norm_pow, Complex.norm_I, one_mul, norm_one,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, one_div, inv_pow,
      div_eq_mul_inv, norm_inv] using h
  have hm := mul_le_mul hd hu (norm_nonneg _) (by positivity)
  have hp : 0 < 4 * Real.pi := by positivity
  unfold phiGradient
  rw [norm_div, norm_mul]
  have he : ‖(4 * Real.pi : ℂ)‖ = 4 * Real.pi := by simp [norm_mul, Real.pi_pos.le]
  rw [he]
  calc
    _ ≤ (|k| * ‖x‖⁻¹ + (‖x‖⁻¹)^2) / (4 * Real.pi) := by
      exact div_le_div_of_nonneg_right (by simpa only [mul_one] using hm) hp.le
    _ = _ := by ring

theorem gradient_integrable_ball (k R : ℝ) (j : Fin 3) :
    IntegrableOn (fun x : Space => phiGradient k x j) (closedBall 0 R) := by
  have h := ((KernelIntegrability.inverse_norm_integrable_ball R).const_mul |k|).add
    (KernelIntegrability.inverse_norm_sq_integrable_ball R)
  apply (h.const_mul (4 * Real.pi)⁻¹).mono' (gradient_measurable k j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => gradient_bound k x j)

theorem gradient_locallyIntegrable (k : ℝ) (j : Fin 3) :
    LocallyIntegrable (fun x : Space => phiGradient k x j) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (gradient_integrable_ball k R j).mono_set hR

theorem phi_weak_partial (k : ℝ) (j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, phiGradient k x j * φ x) = -(∫ x, phi k x * dcoord φ x j) :=
  PointSingularity.weak_partial j (phi k) (fun x => phiGradient k x j)
    (fun x hx => (phi_contDiffAt k x hx).differentiableAt (by simp))
    (fun x hx => phi_partial k x hx j)
    (KernelIntegrability.phi_locallyIntegrable k) (gradient_locallyIntegrable k j) φ hφ hc

end OQ14.KernelGradient

#print axioms OQ14.KernelGradient.gradient_measurable
#print axioms OQ14.KernelGradient.gradient_differentiableAt
#print axioms OQ14.KernelGradient.gradient_bound
#print axioms OQ14.KernelGradient.gradient_integrable_ball
#print axioms OQ14.KernelGradient.gradient_locallyIntegrable
#print axioms OQ14.KernelGradient.phi_weak_partial

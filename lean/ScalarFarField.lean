import ScalarRadiation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual far-field amplitude of a compact scalar source -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarFarField

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.GreenKernel
  OQ14.KernelConvolution OQ14.ScalarRadiation
open scoped Topology InnerProductSpace

theorem ray_norm_ratio_limit (n y : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => ‖r • n - y‖ / r) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => n - r⁻¹ • y) atTop (𝓝 n) := by
    simpa only [zero_smul, sub_zero] using
      (tendsto_const_nhds.sub (tendsto_inv_atTop_zero.smul tendsto_const_nhds) :
        Tendsto (fun r : ℝ => n - r⁻¹ • y) atTop (𝓝 (n - (0 : ℝ) • y)))
  have hnorm := h.norm
  rw [hn] at hnorm
  apply hnorm.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have he : n - r⁻¹ • y = r⁻¹ • (r • n - y) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_eq_mul_inv]
  ring

theorem ray_distance_difference (n y : Space) (hn : ‖n‖ = 1) (r : ℝ) (hr : 0 < r) :
    ‖r • n - y‖ - r =
      (‖y‖^2 / r - 2 * ⟪n, y⟫_ℝ) / (‖r • n - y‖ / r + 1) := by
  have hs := norm_sub_sq_real (r • n) y
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one,
    real_inner_smul_left] at hs
  have hd : ‖r • n - y‖ / r + 1 ≠ 0 := by positivity
  apply (eq_div_iff hd).mpr
  generalize hi : ⟪n, y⟫_ℝ = a at hs ⊢
  field_simp
  nlinarith

theorem ray_distance_difference_limit (n y : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => ‖r • n - y‖ - r) atTop (𝓝 (-⟪n, y⟫_ℝ)) := by
  have hnum : Tendsto (fun r : ℝ => ‖y‖^2 / r - 2 * ⟪n, y⟫_ℝ) atTop
      (𝓝 (-2 * ⟪n, y⟫_ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_sub, neg_mul] using
      ((tendsto_const_nhds.mul tendsto_inv_atTop_zero).sub tendsto_const_nhds :
        Tendsto (fun r : ℝ => ‖y‖^2 * r⁻¹ - 2 * ⟪n, y⟫_ℝ) atTop
          (𝓝 (‖y‖^2 * 0 - 2 * ⟪n, y⟫_ℝ)))
  have hden := (ray_norm_ratio_limit n y hn).add_const 1
  have h := hnum.div hden (by norm_num : (1 : ℝ) + 1 ≠ 0)
  have he : (-2 * ⟪n, y⟫_ℝ) / (1+1) = -⟪n, y⟫_ℝ := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (ray_distance_difference n y hn r hr).symm

def scaledKernel (k r : ℝ) (n y : Space) : ℂ :=
  (r : ℂ) * Complex.exp (-Complex.I * k * r) * phi k (r • n - y)

theorem scaledKernel_formula (k r : ℝ) (n y : Space) :
    scaledKernel k r n y =
      ((‖r • n - y‖ / r : ℝ) : ℂ)⁻¹ *
        Complex.exp (Complex.I * k * (‖r • n - y‖ - r : ℝ)) / (4 * Real.pi) := by
  have he : Complex.exp (-Complex.I * (k : ℂ) * r) *
      Complex.exp (Complex.I * (k : ℂ) * ‖r • n - y‖) =
        Complex.exp (Complex.I * k * (‖r • n - y‖ - r : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [scaledKernel, phi, radial, Complex.ofReal_div, inv_div]
  calc
    _ = ((r : ℂ) / ‖r • n - y‖) *
        (Complex.exp (-Complex.I * (k : ℂ) * r) *
          Complex.exp (Complex.I * (k : ℂ) * ‖r • n - y‖)) / (4 * Real.pi) := by ring
    _ = _ := by rw [he]

theorem scaledKernel_limit (k : ℝ) (n y : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => scaledKernel k r n y) atTop
      (𝓝 (Complex.exp (-Complex.I * k * (⟪n, y⟫_ℝ : ℝ)) / (4 * Real.pi))) := by
  have hratio : Tendsto (fun r : ℝ => ((‖r • n - y‖ / r : ℝ) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (ray_norm_ratio_limit n y hn)
  have hc : Continuous (fun s : ℝ => Complex.exp (Complex.I * k * s)) := by fun_prop
  have hphase := (hc.tendsto (-⟪n, y⟫_ℝ)).comp (ray_distance_difference_limit n y hn)
  have h := ((hratio.inv₀ (by norm_num)).mul hphase).div_const (4 * (Real.pi : ℂ))
  have he : Complex.I * (k : ℂ) * (-⟪n, y⟫_ℝ : ℝ) =
      -Complex.I * k * (⟪n, y⟫_ℝ : ℝ) := by push_cast; ring
  simpa only [Function.comp_def, inv_one, one_mul, he, scaledKernel_formula] using h

theorem scaledKernel_bound (k R r : ℝ) (hR : 0 ≤ R) (hr : 2*R < r)
    (n y : Space) (hn : ‖n‖ = 1) (hy : y ∈ closedBall 0 R) :
    ‖scaledKernel k r n y‖ ≤ 2 / (4 * Real.pi) := by
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hnr : ‖r • n‖ = r := by rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
  have he : ‖Complex.exp (-Complex.I * (k : ℂ) * r)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [scaledKernel, norm_mul, norm_mul, he, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr0, mul_one]
  have hb := phi_source_bound k R hR (r • n) y (by rwa [hnr]) hy
  rw [hnr] at hb
  calc
    _ ≤ r * ((4 * Real.pi)⁻¹ * (2/r)) := mul_le_mul_of_nonneg_left hb hr0.le
    _ = _ := by field_simp; ring

def amplitude (k : ℝ) (ρ : Space → ℂ) (n : Space) : ℂ :=
  ∫ y, ρ y * (Complex.exp (-Complex.I * k * (⟪n, y⟫_ℝ : ℝ)) / (4 * Real.pi))

theorem scaled_response_integral (k r : ℝ) (ρ : Space → ℂ) (n : Space) :
    (r : ℂ) * Complex.exp (-Complex.I * k * r) * response (phi k) ρ (r • n) =
      ∫ y, ρ y * scaledKernel k r n y := by
  unfold response
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [scaledKernel]
  ring

/-- The amplitude is the actual compact-source Fourier integral on the
frequency sphere, obtained as a limit of the actual outgoing potential. -/
theorem response_far_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (n : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-Complex.I * k * r) *
        response (phi k) ρ (r • n)) atTop (𝓝 (amplitude k ρ n)) := by
  simp_rw [scaled_response_integral]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => ‖ρ y‖ * (2 / (4 * Real.pi)))
  · apply Eventually.of_forall
    intro r
    apply hρ.aestronglyMeasurable.mul
    apply AEStronglyMeasurable.const_mul
    exact ((KernelIntegrability.phi_measurable k).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (2*R)] with r hr
    filter_upwards with y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (scaledKernel_bound k R r hR hr n y hn hy)
        (norm_nonneg _)
    · simp [hc y hy]
  · exact hρ.norm.mul_const _
  · filter_upwards with y
    exact tendsto_const_nhds.mul (scaledKernel_limit k n y hn)

end OQ14.ScalarFarField

#print axioms OQ14.ScalarFarField.ray_norm_ratio_limit
#print axioms OQ14.ScalarFarField.ray_distance_difference
#print axioms OQ14.ScalarFarField.ray_distance_difference_limit
#print axioms OQ14.ScalarFarField.scaledKernel_formula
#print axioms OQ14.ScalarFarField.scaledKernel_limit
#print axioms OQ14.ScalarFarField.scaledKernel_bound
#print axioms OQ14.ScalarFarField.scaled_response_integral
#print axioms OQ14.ScalarFarField.response_far_limit

import ComplexExteriorIntegral
import ScalarFarField

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexScalarFar
open Complex MeasureTheory Metric Filter OQ14.Maxwell OQ14.ComplexGreenKernel
  OQ14.ScalarFarField
open scoped Topology InnerProductSpace

def scaledKernel (z : ℂ) (r : ℝ) (n y : Space) : ℂ :=
  (r : ℂ) * Complex.exp (-I*z*r) * phi z (r • n - y)

theorem scaledKernel_formula (z : ℂ) (r : ℝ) (n y : Space) :
    scaledKernel z r n y = ((‖r • n - y‖ / r : ℝ) : ℂ)⁻¹ *
      Complex.exp (I*z*(‖r • n - y‖ - r : ℝ)) / (4 * Real.pi) := by
  have he : Complex.exp (-I*z*r) * Complex.exp (I*z*‖r • n - y‖) =
      Complex.exp (I*z*(‖r • n - y‖ - r : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [scaledKernel, phi, radial, Complex.ofReal_div, inv_div]
  calc
    _ = ((r : ℂ) / ‖r • n - y‖) *
        (Complex.exp (-I*z*r) * Complex.exp (I*z*‖r • n - y‖)) / (4 * Real.pi) := by ring
    _ = _ := by rw [he]

theorem scaledKernel_limit (z : ℂ) (n y : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => scaledKernel z r n y) atTop
      (𝓝 (Complex.exp (-I*z*(⟪n, y⟫_ℝ : ℝ)) / (4 * Real.pi))) := by
  have hratio : Tendsto (fun r : ℝ => ((‖r • n - y‖ / r : ℝ) : ℂ)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, ofReal_one] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp (ray_norm_ratio_limit n y hn)
  have hc : Continuous (fun s : ℝ => Complex.exp (I*z*s)) := by fun_prop
  have hphase := (hc.tendsto (-⟪n, y⟫_ℝ)).comp (ray_distance_difference_limit n y hn)
  have h := ((hratio.inv₀ (by norm_num)).mul hphase).div_const (4 * (Real.pi : ℂ))
  have he : I*z*(-⟪n, y⟫_ℝ : ℝ) = -I*z*(⟪n, y⟫_ℝ : ℝ) := by push_cast; ring
  simpa only [Function.comp_def, inv_one, one_mul, he, scaledKernel_formula] using h

theorem scaledKernel_bound (z : ℂ) (R r : ℝ) (hR : 0 ≤ R) (hr : 2*R < r)
    (n y : Space) (hn : ‖n‖ = 1) (hy : y ∈ closedBall 0 R) :
    ‖scaledKernel z r n y‖ ≤ 2 * Real.exp (‖z‖*R) / (4*Real.pi) := by
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hyb : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hd := abs_norm_sub_norm_le (r • n - y) (r • n)
  rw [hnr] at hd
  have hsub : r • n - y - r • n = -y := by abel
  rw [hsub, norm_neg] at hd
  have hdR : |‖r • n-y‖-r| ≤ R := hd.trans hyb
  have hdist : 0 < ‖r • n-y‖ := by
    have hh := (abs_sub_le_iff.mp hdR).2
    linarith
  have hratio : r / ‖r • n-y‖ ≤ 2 := by
    apply (div_le_iff₀ hdist).2
    have hh := (abs_sub_le_iff.mp hdR).2
    linarith
  have harg : ‖I*z*(‖r • n-y‖-r : ℝ)‖ ≤ ‖z‖*R := by
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hdR (norm_nonneg z)
  have hexp : ‖Complex.exp (I*z*(‖r • n-y‖-r : ℝ))‖ ≤ Real.exp (‖z‖*R) :=
    (ComplexDynamicKernel.exp_norm_bound _).trans (Real.exp_le_exp.mpr harg)
  rw [scaledKernel_formula, norm_div, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hdist hr0)]
  have hpi : 0 < ‖(4 * (Real.pi : ℂ))‖ := norm_pos_iff.mpr (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hinv : (‖r • n-y‖ / r)⁻¹ ≤ 2 := by simpa [inv_div] using hratio
  have hm := mul_le_mul hinv hexp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  apply (div_le_div_of_nonneg_right hm hpi.le).trans_eq
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

def amplitude (z : ℂ) (ρ : Space → ℂ) (n : Space) : ℂ :=
  ∫ y, ρ y * (Complex.exp (-I*z*(⟪n, y⟫_ℝ : ℝ)) / (4 * Real.pi))

theorem phi_measurable (z : ℂ) : Measurable (phi z) := by
  unfold phi radial
  fun_prop

theorem scaled_response_integral (z : ℂ) (r : ℝ) (ρ : Space → ℂ) (n : Space) :
    (r : ℂ) * Complex.exp (-I*z*r) * KernelConvolution.response (phi z) ρ (r • n) =
      ∫ y, ρ y * scaledKernel z r n y := by
  unfold KernelConvolution.response
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [scaledKernel]
  ring

theorem response_far_limit (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (n : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-I*z*r) *
        KernelConvolution.response (phi z) ρ (r • n)) atTop (𝓝 (amplitude z ρ n)) := by
  simp_rw [scaled_response_integral]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => ‖ρ y‖ * (2 * Real.exp (‖z‖*R) / (4*Real.pi)))
  · apply Eventually.of_forall
    intro r
    apply hρ.aestronglyMeasurable.mul
    apply AEStronglyMeasurable.const_mul
    exact ((phi_measurable z).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (2*R)] with r hr
    filter_upwards with y
    by_cases hy : y ∈ closedBall (0 : Space) R
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (scaledKernel_bound z R r hR hr n y hn hy) (norm_nonneg _)
    · simp [hc y hy]
  · exact hρ.norm.mul_const _
  · filter_upwards with y
    exact tendsto_const_nhds.mul (scaledKernel_limit z n y hn)

#print axioms OQ14.ComplexScalarFar.response_far_limit
#print axioms OQ14.ComplexScalarFar.scaledKernel_bound
#print axioms OQ14.ComplexScalarFar.scaledKernel_formula
#print axioms OQ14.ComplexScalarFar.scaledKernel_limit
end OQ14.ComplexScalarFar





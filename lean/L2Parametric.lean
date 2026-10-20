import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.L2Parametric

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re])

/-- A genuine L2 derivative follows from pointwise derivatives with a local
uniform L2 majorant. The difference quotients converge in the L2 norm. -/
theorem hasDerivAt_toLp (F G : ℂ → α → ℂ)
    (hF : ∀ z, MemLp (F z) 2 μ) (z₀ : ℂ) (hG : MemLp (G z₀) 2 μ)
    (hd : ∀ x z, HasDerivAt (fun w => F w x) (G z x) z)
    (b : α → ℝ) (hb : MemLp b 2 μ)
    (hbound : ∀ x z, z ∈ ball z₀ 1 → ‖G z x‖ ≤ b x) :
    HasDerivAt (fun z => (hF z).toLp (F z)) (hG.toLp (G z₀)) z₀ := by
  let f : ℂ → Lp ℂ 2 μ := fun z => (hF z).toLp (F z)
  let g : Lp ℂ 2 μ := hG.toLp (G z₀)
  let q : ℂ → α → ℂ := fun z x => (z - z₀)⁻¹ * (F z x - F z₀ x) - G z₀ x
  have hz₀ : z₀ ∈ ball z₀ 1 := by simp
  have hb0 (x : α) : 0 ≤ b x := (norm_nonneg _).trans (hbound x z₀ hz₀)
  have hqbound (z : ℂ) (hz : z ∈ ball z₀ 1) (x : α) : ‖q z x‖ ≤ 2 * b x := by
    have hsub : ‖F z x - F z₀ x‖ ≤ b x * ‖z - z₀‖ :=
      (convex_ball z₀ (1 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun w _ => (hd x w).hasDerivWithinAt) (fun w hw => hbound x w hw) hz₀ hz
    have hslope : ‖(z - z₀)⁻¹ * (F z x - F z₀ x)‖ ≤ b x := by
      by_cases he : z = z₀
      · simp [he, hb0 x]
      rw [norm_mul, norm_inv]
      calc
        _ ≤ ‖z - z₀‖⁻¹ * (b x * ‖z - z₀‖) :=
          mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (norm_nonneg _))
        _ = b x := by field_simp [sub_ne_zero.mpr he]
    exact (norm_sub_le _ _).trans (by linarith [hbound x z₀ hz₀])
  have hmeas (z : ℂ) : AEStronglyMeasurable (fun x => ‖q z x‖^2) μ := by
    exact ((((hF z).aestronglyMeasurable.sub (hF z₀).aestronglyMeasurable).const_mul
      (z - z₀)⁻¹).sub hG.aestronglyMeasurable).norm.pow 2
  have hbint : Integrable (fun x => (2 * b x)^2) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
    simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using hi.const_mul ((2 : ℝ)^2)
  have hlim : Tendsto (fun z => ∫ x, ‖q z x‖^2 ∂μ) (𝓝[≠] z₀) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (fun x => (2 * b x)^2)
      (Eventually.of_forall hmeas)
      (by
        filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds z₀ zero_lt_one)] with z hz
        exact ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hqbound z hz x) 2))
      hbint
      (ae_of_all _ (fun x => by
        have hh := ((hasDerivAt_iff_tendsto_slope.mp (hd x z₀)).sub_const (G z₀ x)).norm.pow 2
        simpa only [q, slope, smul_eq_mul, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using hh))
    simpa only [integral_zero] using hh
  have hnorm (z : ℂ) : ‖(z - z₀)⁻¹ • (f z - f z₀) - g‖^2 = ∫ x, ‖q z x‖^2 ∂μ := by
    rw [norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((z-z₀)⁻¹ • (f z - f z₀)) g,
      Lp.coeFn_smul (z-z₀)⁻¹ (f z - f z₀), Lp.coeFn_sub (f z) (f z₀),
      (hF z).coeFn_toLp, (hF z₀).coeFn_toLp, hG.coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    change (f z : α → ℂ) x = F z x at h4
    change (f z₀ : α → ℂ) x = F z₀ x at h5
    change (g : α → ℂ) x = G z₀ x at h6
    simp only [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4, h5, h6, q]
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (hlim.congr' (Eventually.of_forall (fun z => (hnorm z).symm))).sqrt
  simpa only [slope, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hh

end OQ14.L2Parametric

#print axioms OQ14.L2Parametric.norm_sq_integral
#print axioms OQ14.L2Parametric.hasDerivAt_toLp

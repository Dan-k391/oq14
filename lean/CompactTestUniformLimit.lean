import HelmholtzKernelSmoothing

/-! Actual compactly supported integral pairings preserve uniform limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CompactTestUniformLimit
open MeasureTheory Filter Set OQ14.Maxwell OQ14.HelmholtzKernelSmoothing
open scoped Topology

theorem integral_mul_tendsto {ι : Type*} (l : Filter ι) (Ω : Set Space) (hΩ : IsOpen Ω)
    (F : ι → Space → ℂ) (f q : Space → ℂ)
    (hF : ∀ n, ContinuousOn (F n) Ω) (hf : ContinuousOn f Ω)
    (hq : Continuous q) (hc : HasCompactSupport q) (hs : tsupport q ⊆ Ω)
    (hlim : TendstoUniformlyOn F f l (tsupport q)) :
    Tendsto (fun n => ∫ y, F n y*q y) l (𝓝 (∫ y, f y*q y)) := by
  have hI : Integrable q := hq.integrable_of_hasCompactSupport hc
  have hiF (n : ι) : Integrable (fun y => F n y*q y) :=
    (localized_product_continuous Ω hΩ (F n) q (hF n) hq hs).integrable_of_hasCompactSupport hc.mul_left
  have hif : Integrable (fun y => f y*q y) :=
    (localized_product_continuous Ω hΩ f q hf hq hs).integrable_of_hasCompactSupport hc.mul_left
  let I : ℝ := ∫ y, ‖q y‖
  have hI0 : 0 ≤ I := integral_nonneg (fun y => norm_nonneg _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(I+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn
  rw [dist_eq_norm,← integral_sub (hiF n) hif]
  have hb : ∀ᵐ y ∂volume, ‖F n y*q y-f y*q y‖ ≤ δ*‖q y‖ := by
    filter_upwards with y
    by_cases hy : y ∈ tsupport q
    · rw [← sub_mul,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [dist_eq_norm,norm_sub_rev] using (hn y hy).le
    · simp only [image_eq_zero_of_nmem_tsupport hy,mul_zero,sub_self,norm_zero,le_refl]
  calc
    _ ≤ ∫ y, ‖F n y*q y-f y*q y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, δ*‖q y‖ := integral_mono_ae ((hiF n).sub hif).norm (hI.norm.const_mul δ) hb
    _ = δ*I := integral_const_mul _ _
    _ < ε := by
      have he : δ*(I+1)=ε := div_mul_cancel₀ ε (by linarith : I+1≠0)
      nlinarith

end OQ14.CompactTestUniformLimit
#print axioms OQ14.CompactTestUniformLimit.integral_mul_tendsto

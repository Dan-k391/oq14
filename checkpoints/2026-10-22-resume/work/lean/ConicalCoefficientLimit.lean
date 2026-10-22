import ConicalCoefficientIdentity
import ConicalCorrectionBounds

/-! Genuine vanishing of the radial particular contribution in annular coefficient extraction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ConicalCoefficientLimit
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume OQ14.ConicalCoefficientIdentity
  OQ14.ConicalAnnularCoefficient OQ14.ConicalCorrectionBounds
open scoped Topology

theorem particularPair_norm_bound (p : Data) (hν : p.exponent < 1) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ,
      |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut → ‖particularPair p k ζ‖ ≤ k^2*C := by
  obtain ⟨C,hC,hb⟩ := particular_quadratic_bound p hν p.cutoff.rIn
  have hi : IntegrableOn (fun r : ℝ => r^2*|ζ r|) (Ioi (0 : ℝ)) :=
    ((continuous_id.pow 2).mul hζ.continuous.abs).integrable_of_hasCompactSupport (μ := volume)
      (hc.norm.mul_left) |>.integrableOn
  let I : ℝ := ∫ r in Ioi (0 : ℝ), r^2*|ζ r|
  have hI : 0 ≤ I := integral_nonneg (fun r => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  refine ⟨‖(p.eigenvalue : ℂ)‖*C*I,mul_nonneg (mul_nonneg (norm_nonneg _) hC) hI,?_⟩
  intro k hk
  have hpair : ‖∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.particular p.exponent
      (ConicalCorrectionMoments.radialCorrection p k) (ConicalCorrectionMoments.tangentCorrection p k) r‖ ≤ k^2*C*I := by
    dsimp only [I]
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hi.const_mul (k^2*C))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hz : ζ r=0
    · simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero,abs_zero]
      exact le_rfl
    · have hri := (hs (subset_tsupport ζ hz)).2
      rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      have hh := mul_le_mul_of_nonneg_left (hb k hk r ⟨hr,hri.le⟩) (mul_nonneg hr.le (abs_nonneg (ζ r)))
      convert hh using 1
      ring
  rw [particularPair,norm_mul]
  exact (mul_le_mul_of_nonneg_left hpair (norm_nonneg _)).trans_eq (by dsimp only [I]; ring)

theorem particularPair_tendsto (p : Data) (hν : p.exponent < 1) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    Tendsto (fun k => particularPair p k ζ) (𝓝 (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hb⟩ := particularPair_norm_bound p hν ζ hζ hc hs
  have he : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (DynamicStaticLimit.frequencyRadius_positive (coefficient p) p.cutoff.rOut)] with k hk
    exact (show |k| < DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut from by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk).le
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hl : Tendsto (fun k : ℝ => k^2*C) (𝓝 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 (0 : ℝ)) (𝓝 0)).pow 2).mul_const C
  exact squeeze_zero' (Filter.Eventually.of_forall (fun k => norm_nonneg _)) (he.mono (fun k hk => hb k hk)) hl

theorem numerator_tendsto (p : Data) (hν : p.exponent < 1) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    Tendsto (fun k => gradientPair p k ζ hζ hc-particularPair p k ζ) (𝓝 (0 : ℝ))
      (𝓝 (fieldPair p ζ hζ hc (electric p))) := by
  simpa only [sub_zero] using (gradientPair_tendsto p ζ hζ hc hs).sub (particularPair_tendsto p hν ζ hζ hc hs)

end OQ14.ConicalCoefficientLimit

#print axioms OQ14.ConicalCoefficientLimit.particularPair_norm_bound
#print axioms OQ14.ConicalCoefficientLimit.particularPair_tendsto
#print axioms OQ14.ConicalCoefficientLimit.numerator_tendsto

import ConicalStaticCoefficient
import ConicalCoefficientLimit

/-! Actual positive-frequency retention of a nonzero conical singular coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCoefficientRetention
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume OQ14.ConicalStaticCoefficient
  OQ14.ConicalCoefficientLimit OQ14.ConicalCoefficientIdentity OQ14.ConicalAnnularCoefficient
  OQ14.ConicalProjectedDerivative
open scoped Topology

def annularBump (p : Data) : ContDiffBump (p.cutoff.rIn/2 : ℝ) :=
  ⟨p.cutoff.rIn/8,p.cutoff.rIn/4,by linarith [p.cutoff.rIn_pos],by linarith [p.cutoff.rIn_pos]⟩

theorem annularBump_support (p : Data) : tsupport (annularBump p : ℝ → ℝ) ⊆ Ioo (0 : ℝ) p.cutoff.rIn := by
  intro r hr
  rw [(annularBump p).tsupport_eq] at hr
  have hh : |r-p.cutoff.rIn/2| ≤ p.cutoff.rIn/4 := by
    simpa only [mem_closedBall,Real.dist_eq,annularBump] using hr
  have hb := abs_le.mp hh
  constructor <;> linarith [p.cutoff.rIn_pos]

theorem eventually_nonzero_coefficient (p : Data) (hν : p.exponent < 1) :
    ∀ᶠ k : ℝ in 𝓝 0, k≠0 → ∃ c : ℂ, c≠0 ∧
      projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] fun r =>
        c*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
          (ConicalCorrectionMoments.radialCorrection p k) (ConicalCorrectionMoments.tangentCorrection p k) r := by
  let ζ : ℝ → ℝ := annularBump p
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (annularBump p).contDiff
  have hc : HasCompactSupport ζ := (annularBump p).hasCompactSupport
  have hs := annularBump_support p
  have hne := static_pairing_ne_zero p hν ζ hζ hc hs (fun r => (annularBump p).nonneg)
    (p.cutoff.rIn/2) (by linarith [p.cutoff.rIn_pos]) (by
      have hh : ζ (p.cutoff.rIn/2)=1 := (annularBump p).one_of_mem_closedBall (by
        simp only [mem_closedBall,dist_self]; exact (annularBump p).rIn_pos.le)
      rw [hh]; exact one_ne_zero)
  have ht := numerator_tendsto p hν ζ hζ hc hs
  have hN : ∀ᶠ k : ℝ in 𝓝 0, gradientPair p k ζ hζ hc-particularPair p k ζ≠0 :=
    ht.eventually ((isClosed_singleton (x := (0 : ℂ))).isOpen_compl.mem_nhds hne)
  have hfreq : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (DynamicStaticLimit.frequencyRadius_positive (coefficient p) p.cutoff.rOut)] with k hk
    exact (show |k| < DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut from by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk).le
  filter_upwards [hN,hfreq] with k hn hk
  intro hk0
  obtain ⟨c,he,hex⟩ := coefficient_identity p hν k hk0 hk ζ hζ hc hs
  refine ⟨c,?_,he⟩
  intro hz
  rw [hz,mul_zero,zero_mul,zero_add] at hex
  exact hn (sub_eq_zero.mpr hex)

theorem positive_frequency_nonzero_coefficient (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∃ c : ℂ, c≠0 ∧
      projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] fun r =>
        c*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
          (ConicalCorrectionMoments.radialCorrection p k) (ConicalCorrectionMoments.tangentCorrection p k) r := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (eventually_nonzero_coefficient p hν)
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  have hm : k ∈ ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd
  exact hsub hm hk.ne'

end OQ14.ConicalCoefficientRetention

#print axioms OQ14.ConicalCoefficientRetention.annularBump_support
#print axioms OQ14.ConicalCoefficientRetention.eventually_nonzero_coefficient
#print axioms OQ14.ConicalCoefficientRetention.positive_frequency_nonzero_coefficient

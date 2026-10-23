import ConicalStaticCoefficient
import ConicalSeparatedLimit

/-! Actual positive-frequency retention of a nonzero conical singular coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalSeparatedRetention
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume OQ14.ConicalStaticCoefficient
  OQ14.ConicalSeparatedLimit OQ14.ConicalSeparatedIdentity OQ14.ConicalAnnularCoefficient
  OQ14.ConicalGraphProjection
open scoped Topology

def annularBump (a : ℝ) (ha : 0 < a) : ContDiffBump (a/2 : ℝ) :=
  ⟨a/8,a/4,by linarith [ha],by linarith [ha]⟩

theorem annularBump_support (a : ℝ) (ha : 0 < a) : tsupport (annularBump a ha : ℝ → ℝ) ⊆ Ioo (0 : ℝ) a := by
  intro r hr
  rw [(annularBump a ha).tsupport_eq] at hr
  have hh : |r-a/2| ≤ a/4 := by
    simpa only [mem_closedBall,Real.dist_eq,annularBump] using hr
  have hb := abs_le.mp hh
  constructor <;> linarith [ha]

theorem eventually_nonzero_coefficient (p : Data) (a : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∀ᶠ k : ℝ in 𝓝 0, k≠0 → ∃ c : ℂ, c≠0 ∧
      projected p (ConicalGradientGraph.separated p a k hai) =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun r =>
        c*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
          (ConicalSeparatedCorrection.radialCorrection p a k) (ConicalSeparatedCorrection.tangentCorrection p a k) r := by
  let ζ : ℝ → ℝ := annularBump a ha
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (annularBump a ha).contDiff
  have hc : HasCompactSupport ζ := (annularBump a ha).hasCompactSupport
  have hs := annularBump_support a ha
  have hne := static_pairing_ne_zero p hν ζ hζ hc (hs.trans (Ioo_subset_Ioo_right hai.le)) (fun r => (annularBump a ha).nonneg)
    (a/2) (by linarith [ha]) (by
      have hh : ζ (a/2)=1 := (annularBump a ha).one_of_mem_closedBall (by
        simp only [mem_closedBall,dist_self]; exact (annularBump a ha).rIn_pos.le)
      rw [hh]; exact one_ne_zero)
  have ht := numerator_tendsto p a ha.le hai hν ζ hζ hc hs
  have hN : ∀ᶠ k : ℝ in 𝓝 0, ConicalSeparatedPairing.gradientPair p a k hai ζ hζ hc-particularPair p a k ζ≠0 :=
    ht.eventually ((isClosed_singleton (x := (0 : ℂ))).isOpen_compl.mem_nhds hne)
  have hfreq : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (DynamicStaticLimit.frequencyRadius_positive (ConicalSeparatedSource.material p a) a)] with k hk
    exact (show |k| < DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a from by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk).le
  filter_upwards [hN,hfreq] with k hn hk
  intro hk0
  obtain ⟨c,he,hex⟩ := coefficient_identity p a k ha hai hν hk0 hk ζ hζ hc hs
  refine ⟨c,?_,he⟩
  intro hz
  rw [hz,mul_zero,zero_mul,zero_add] at hex
  exact hn (sub_eq_zero.mpr hex)

theorem positive_frequency_nonzero_coefficient (p : Data) (a : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∃ c : ℂ, c≠0 ∧
      projected p (ConicalGradientGraph.separated p a k hai) =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun r =>
        c*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
          (ConicalSeparatedCorrection.radialCorrection p a k) (ConicalSeparatedCorrection.tangentCorrection p a k) r := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (eventually_nonzero_coefficient p a ha hai hν)
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  have hm : k ∈ ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd
  exact hsub hm hk.ne'

end OQ14.ConicalSeparatedRetention

#print axioms OQ14.ConicalSeparatedRetention.annularBump_support
#print axioms OQ14.ConicalSeparatedRetention.eventually_nonzero_coefficient
#print axioms OQ14.ConicalSeparatedRetention.positive_frequency_nonzero_coefficient

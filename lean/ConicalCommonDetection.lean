import ConicalCommonCorrectionStability

/-! A nonzero intrinsic cone coefficient is detected by a positive annular bump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonDetection
open MeasureTheory Set Metric OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
abbrev Data := ConicalStaticVolume.Data

theorem numerator_ne_zero_of_coefficient (p : Data) (b r : ℝ) (hb : 0 < b) (hr : 0 < r) (hrb : r < b)
    (hbi : b < p.cutoff.rIn) (hν : p.exponent < 1) (s : System p b)
    (hq : ConicalIntrinsicCoefficient.coefficient s hb hbi hν ≠ 0) :
    let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump r hr
    ConicalCoefficientStability.numerator s ζ (ConicalSeparatedRetention.annularBump r hr).contDiff
      (ConicalSeparatedRetention.annularBump r hr).hasCompactSupport ≠ 0 := by
  let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump r hr
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (ConicalSeparatedRetention.annularBump r hr).contDiff
  have hc : HasCompactSupport ζ := (ConicalSeparatedRetention.annularBump r hr).hasCompactSupport
  have hs : tsupport ζ ⊆ Ioo (0 : ℝ) r := ConicalSeparatedRetention.annularBump_support r hr
  have hp := ConicalStaticCoefficient.radialFactor_re_positive p ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right (hrb.trans hbi).le))
    (fun _ => (ConicalSeparatedRetention.annularBump r hr).nonneg) (r/2) (by linarith)
    (by
      have hv : ζ (r/2) = 1 := (ConicalSeparatedRetention.annularBump r hr).one_of_mem_closedBall (by
        simp only [mem_closedBall, dist_self]; exact (ConicalSeparatedRetention.annularBump r hr).rIn_pos.le)
      rw [hv]; exact one_ne_zero)
  have hrad : ConicalLocalCoefficient.radialFactor p ζ ≠ 0 := by
    intro hz
    change 0 < (ConicalCoefficientIdentity.radialFactor p ζ).re at hp
    have he : ConicalLocalCoefficient.radialFactor p ζ = ConicalCoefficientIdentity.radialFactor p ζ := rfl
    have hz' : ConicalCoefficientIdentity.radialFactor p ζ = 0 := he.symm.trans hz
    simp [hz'] at hp
  obtain ⟨q, hqspec, he⟩ := ConicalLocalCoefficient.coefficient_identity s hb hbi hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hrb.le))
  have hqeq := ConicalIntrinsicCoefficient.coefficient_unique s hb hbi hν q hqspec
  have hq0 : q ≠ 0 := by rw [hqeq]; exact hq
  have hlambda : (p.eigenvalue : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ConicalProjectedDerivative.eigenvalue_pos p).ne'
  change ConicalLocalCoefficient.gradientPair s ζ hζ hc - ConicalLocalCoefficient.particularPair s ζ ≠ 0
  rw [he]
  intro hz
  have hh : (p.eigenvalue : ℂ) * q * ConicalLocalCoefficient.radialFactor p ζ = 0 := by linear_combination hz
  exact (mul_ne_zero (mul_ne_zero hlambda hq0) hrad) hh

theorem coefficient_ne_zero_of_numerator (p : Data) (b : ℝ) (hb : 0 < b)
    (hbi : b < p.cutoff.rIn) (hν : p.exponent < 1) (s : System p b)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b)
    (hn : ConicalCoefficientStability.numerator s ζ hζ hc ≠ 0) :
    ConicalIntrinsicCoefficient.coefficient s hb hbi hν ≠ 0 := by
  obtain ⟨q,hq,he⟩ := ConicalLocalCoefficient.coefficient_identity s hb hbi hν ζ hζ hc hs
  have hqeq := ConicalIntrinsicCoefficient.coefficient_unique s hb hbi hν q hq
  intro hz
  have hq0 : q = 0 := hqeq.trans hz
  apply hn
  change ConicalLocalCoefficient.gradientPair s ζ hζ hc - ConicalLocalCoefficient.particularPair s ζ = 0
  rw [he, hq0]
  ring

end OQ14.ConicalCommonDetection
#print axioms OQ14.ConicalCommonDetection.numerator_ne_zero_of_coefficient
#print axioms OQ14.ConicalCommonDetection.coefficient_ne_zero_of_numerator

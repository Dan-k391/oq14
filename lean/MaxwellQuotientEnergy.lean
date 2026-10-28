import MaxwellDifferenceQuotient
import WeakPoynting.MagneticCompactness

/-! Uniform difference-quotient control from the actual local Maxwell energy. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellQuotientEnergy
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.WeakTranslations OQ14.CurlCutoff

theorem cutoff_quotient_energy {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM0 : 0 ≤ M)
    (hvχ : ∀ x, ‖χ.function x‖ ≤ A) (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B)
    (k : ℝ) (hk : k ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M) :
    ∀ i j (h : ℝ), h ≠ 0 →
      ‖MaxwellDifferenceQuotient.quotient
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1) j) i h‖ ≤
      3 * (3 * (A * (|k| * M * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
        (3 * B * ‖H.val.1‖)^2 + 1) := by
  obtain ⟨G,hG,henergy⟩ := RegularityBounds.maxwell_cutoff_h1_bound
    hΩ χ hχ hA hB hM0 hvχ hdχ k hk ε E H hM hε
  intro i j h hh
  have hcomp := LocalRegularity.cutoff_extend_compact hΩ χ H.val.1 j
  have hq := MaxwellDifferenceQuotient.quotient_bound hcomp (fun l => hG (l,j)) i h hh
  exact hq.trans (MagneticCompactness.derivative_coordinate_sum_bound henergy j)

end OQ14.MaxwellQuotientEnergy
#print axioms OQ14.MaxwellQuotientEnergy.cutoff_quotient_energy

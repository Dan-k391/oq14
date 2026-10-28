import ConicalCommonGaugeIdentity
import CommonInputAvoidance

/-! A single normalized angular input once the actual common-material functionals are nonzero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonSingleInput
open MeasureTheory Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (p : ι → Data) (a b : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))
  (R k : ℝ) (hR0 : 0 ≤ R) (hk : 0 < k)
  (hb : ∀ i, b i ≤ a i) (hai : ∀ i, a i < (p i).cutoff.rIn)
  (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
  (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
  (hb0 : ∀ i, 0 < b i) (hν : ∀ i, (p i).exponent < 1)

def functional (i : ι) : Input →ₗ[ℂ] ℂ :=
  ConicalCommonAngular.coefficientLinear p a center B hB hcontrast ha hsep i R k (b i) hR0 hk.ne'
    (hb i) (hai i) hfreq hR (hb0 i) (hν i)

omit [DecidableEq ι] in
theorem normalized_common_input (hne : ∀ i, functional p a b center B hB hcontrast ha hsep R k hR0 hk hb hai hfreq hR hb0 hν i ≠ 0) :
    ∃ d : Input, d ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k d) atTop (𝓝 1) ∧
      (∀ i, ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k (b i) hR0 hk.ne'
        (hb i) (hai i) hfreq hR (hb0 i) (hν i) d ≠ 0) ∧
      MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))
        (ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d))
        (ConicalCommonEntire.magnetic p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d)) := by
  obtain ⟨d,hd,hpower,hq⟩ := CommonInputAvoidance.exists_normalized k hk
    (functional p a b center B hB hcontrast ha hsep R k hR0 hk hb hai hfreq hR hb0 hν) hne
  exact ⟨d,hd,hpower,hq,ConicalCommonEntire.maxwell p a center B hB hcontrast ha hsep R k hR0 hfreq hR _⟩

end OQ14.ConicalCommonSingleInput
#print axioms OQ14.ConicalCommonSingleInput.normalized_common_input

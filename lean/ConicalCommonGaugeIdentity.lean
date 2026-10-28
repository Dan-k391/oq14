import ConicalCommonDetection

/-! Gauge independence for actual common-material angular coefficients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonGaugeIdentity
open MeasureTheory Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem coefficient_eq_fixed (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i) (hb0 : 0 < b) (hν : (p i).exponent < 1)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j, Continuous (fun x => J x j))
    (heJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x) :
    ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k b hR0 hk hb.le (hai i) hfreq hR hb0 hν d =
      ConicalIntrinsicCoefficient.coefficient
        (ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ)
        hb0 (hb.trans (hai i)) hν := by
  have htot : ∀ j : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate
        (ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ) j x =
      (1 : ℂ) * ConicalProjectionData.totalCoordinate
        (ConicalCommonAngular.system p a center B hB hcontrast ha hsep i R k b hR0 hk hb.le (hai i) hfreq hR d) j x := by
    intro j
    filter_upwards [ConicalCommonFixedGauge.system_actual p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ j,
      ConicalCommonEntire.system_actual p a center B hB hcontrast ha hsep i R k b hR0 hk hb.le (hai i) hfreq hR (FiniteAngularHerglotz.incident k d) j]
      with x hf he hx
    dsimp only [ConicalCommonAngular.system]
    rw [hf hx, he hx, one_mul, add_comm]
  have h := ConicalIntrinsicCoefficient.coefficient_scaled _ _ hb0 (hb.trans (hai i)) hν 1 htot
  simpa only [one_mul, ConicalCommonAngular.coefficient, ConicalCommonAngular.system] using h.symm

end OQ14.ConicalCommonGaugeIdentity
#print axioms OQ14.ConicalCommonGaugeIdentity.coefficient_eq_fixed

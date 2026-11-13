import Packet05ActualChartFields

/-! The named fixed-chart modal potential and correction recover the literal
physical electric field on the common outer plateau. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ActualFieldIdentity
open MeasureTheory Metric Set Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph
  Packet06ConcreteModalRounding Packet05ActualChartFields
abbrev Space := Maxwell.Space

theorem actual_field_identity {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (j : ℕ) (hz : z j ≠ 0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0) :
    ∀ k, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) Packet05FixedCollarAtlas.outer.rIn →
      gradient Packet05FixedCollarAtlas.outer (potential n hn g η hη z v j) k x +
      Packet06ScalarGaussLocalization.correction Packet05FixedCollarAtlas.outer
        (correction n hn g η hη z v j) (correction_continuous n hn g η hη z v j) k x =
      Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k := by
  have h := Packet06MaxwellScalarEquation.actual_scalar_equation (rounded n hn g η hη j) (z j) hz 1 (v j)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j) hmode Packet05FixedCollarAtlas.outer
  exact h.2.2.2.1

end OQ14.Packet05ActualFieldIdentity
#print axioms OQ14.Packet05ActualFieldIdentity.actual_field_identity

import Packet05ActualChartUniformInputs

/-! Named actual mode fields used in the fixed-chart family bootstrap. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ActualChartFields
open Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph Packet05FiniteFixedAtlas
  Packet06ConcreteModalRounding Packet05ChartWeakGradient Packet05ChartWeakDivergence Packet05GraphPullback
  Packet05GraphH1Pullback Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence Packet05FlatWeight

def potential {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (j : ℕ) : PotentialData :=
  let c := rounded n hn g η hη j
  Packet06ComplexConePotential.potentialData (z j) 1 (StaticCoefficient.sqrtMultiplier c (v j))
    (DynamicVolume.source c (v j))
    (DynamicVolume.source_zero c (v j) 1 (Packet05RoundedModeSupport.rounded_support n hn g η hη j))
    (StaticNewton.material_source_ae c (v j))

def correction {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (j : ℕ) : Field :=
  Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j))

theorem correction_continuous {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (j : ℕ) :
    ∀ k, Continuous (fun x => correction n hn g η hη z v j x k) :=
  Packet06ComplexPotential.correction_continuous (z j) 1
    (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
    (DynamicVolume.source (rounded n hn g η hη j) (v j))
    (DynamicVolume.source_zero (rounded n hn g η hη j) (v j) 1 (Packet05RoundedModeSupport.rounded_support n hn g η hη j))
    (StaticNewton.material_source_ae (rounded n hn g η hη j) (v j))

def scalar {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (chart : Chart n hn g η hη) (j : ℕ) : L2Scalar :=
  pullback chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide)).continuous
    (chartPull chart.up chart.axis (value Packet05FixedCollarAtlas.outer (potential n hn g η hη z v j)))

def scalarGradient {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (chart : Chart n hn g η hη) (B : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B) (j : ℕ) : L2Vector :=
  pulledGradient chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide))
    (chartVector chart.up chart.axis (gradient Packet05FixedCollarAtlas.outer (potential n hn g η hη z v j))) (fun _ => B) hB

def graphCorrection {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (chart : Chart n hn g η hη) (j : ℕ) : L2Vector :=
  chartVector chart.up chart.axis (Packet06ScalarGaussLocalization.correction Packet05FixedCollarAtlas.outer
    (correction n hn g η hη z v j) (correction_continuous n hn g η hη z v j))

def graphForcing {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Packet06ConcreteModalGeometry.Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (chart : Chart n hn g η hη) (B : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B) (j : ℕ) : L2Vector :=
  fun k => -mulWeight chart.jump chart.jump_nonneg
    (transformedFlux chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide))
      (graphCorrection n hn g η hη z v chart j) (fun _ => B) hB k)

end OQ14.Packet05ActualChartFields
#print axioms OQ14.Packet05ActualChartFields.correction_continuous

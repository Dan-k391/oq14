import Packet05FixedChartActualEquation
import Packet05UniformMaterialScalarGraph
import Packet05RoundedCorrectionBounds

/-! Uniform actual graph scalar and gradient bounds on a fixed collar chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05FixedChartUniformScalar
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph
  Packet05ChartWeakGradient Packet05ChartWeakDivergence Packet05GraphPullback Packet05GraphSlopeMultiplier
  Packet05GraphH1Pullback Packet05FiniteFixedAtlas Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_chart_uniform_scalar {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hz : Tendsto z atTop (𝓝 z0)) (hv : Tendsto v atTop (𝓝 v0))
    (B : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j,
      let c := rounded n hn g η hη j
      let hc := Packet05RoundedModeSupport.rounded_support n hn g η hη j
      let U := Packet06ComplexConePotential.potentialData (z j) 1 (StaticCoefficient.sqrtMultiplier c (v j))
        (DynamicVolume.source c (v j)) (DynamicVolume.source_zero c (v j) 1 hc) (StaticNewton.material_source_ae c (v j))
      let hg : ContDiff ℝ 2 chart.graph := chart.regular.of_le (by decide)
      let vchart := pullback chart.graph hg.continuous (chartPull chart.up chart.axis (value Packet05FixedCollarAtlas.outer U))
      let C := pulledGradient chart.graph hg (chartVector chart.up chart.axis (gradient Packet05FixedCollarAtlas.outer U)) (fun _ => B) hB
      ‖vchart‖ ≤ K ∧ ∀ i, ‖C i‖ ≤ K := by
  obtain ⟨Z,L,Bmat,hZ,hL,_,hzB,hvB,hBmat⟩ :=
    Packet05RoundedCorrectionBounds.rounded_family_envelope n hn g η hη z v z0 v0 hz hv
  exact Packet05UniformMaterialScalarGraph.material_family_scalar_graph
    (rounded n hn g η hη) z (fun j => (v j : VectorFourier.VectorL2)) 1 Z Bmat L B
    (by norm_num) hZ hL (Packet05RoundedModeSupport.rounded_support n hn g η hη) hBmat hzB hvB
    Packet05FixedCollarAtlas.outer chart.graph (chart.regular.of_le (by decide)) hB chart.up chart.axis

end OQ14.Packet05FixedChartUniformScalar
#print axioms OQ14.Packet05FixedChartUniformScalar.fixed_chart_uniform_scalar

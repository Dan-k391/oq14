import Packet05RoundedModeSupport
import Packet05FiniteFixedAtlas
import Packet05ActualHostModeGraph

/-! Every fixed collar chart carries the actual regional scalar equation for
all sufficiently late members of the rounded complex-mode family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05FixedSubchartEquation
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph
  Packet05RegionalDivergence Packet05ChartBasis Packet05ChartWeakGradient Packet05ChartWeakDivergence
  Packet05GraphPullback Packet05GraphPiolaCompact Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05GraphH1Pullback Packet05PhysicalGraphChart Packet05GraphChartMap Packet05FlatWeight
  Packet05ScalarDielectricFlux Packet05FiniteFixedAtlas Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventual_actual_subchart_equation {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (u : ℕ → VectorFourier.VectorL2)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (u j)=0)
    (Bs : Fin 3 → ℝ) (hBs : ∀ k x, ‖slopeC chart.graph k x‖ ≤ Bs k)
    (hdi : ∀ k l, MemLp (fun x => dcoord (slopeC chart.graph k) x l) ⊤ volume)
    (hdd : ∀ k l m, MemLp (fun x => dcoord (fun y => dcoord (slopeC chart.graph k) y l) x m) ⊤ volume)
    (W : Set Space) (hW : W ⊆ chart.flat)
    (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ W, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ)) :
    ∀ᶠ j in atTop,
      let c := rounded n hn g η hη j
      let hc := Packet05RoundedModeSupport.rounded_support n hn g η hη j
      let χ := Packet05FixedCollarAtlas.outer
      let U := Packet06ComplexConePotential.potentialData (z j) 1 (StaticCoefficient.sqrtMultiplier c (u j))
        (DynamicVolume.source c (u j)) (DynamicVolume.source_zero c (u j) 1 hc) (StaticNewton.material_source_ae c (u j))
      let Wp := Packet06ComplexPotential.correction (z j) (DynamicVolume.source c (u j))
      let hWp := Packet06ComplexPotential.correction_continuous (z j) 1 (StaticCoefficient.sqrtMultiplier c (u j))
        (DynamicVolume.source c (u j)) (DynamicVolume.source_zero c (u j) 1 hc) (StaticNewton.material_source_ae c (u j))
      let hg : ContDiff ℝ 2 chart.graph := chart.regular.of_le (by decide)
      let v := pullback chart.graph hg.continuous (chartPull chart.up chart.axis (value χ U))
      let C := pulledGradient chart.graph hg (chartVector chart.up chart.axis (gradient χ U)) Bs hBs
      let Q := chartVector chart.up chart.axis (Packet06ScalarGaussLocalization.correction χ Wp hWp)
      let F : L2Vector := fun k => -mulWeight chart.jump chart.jump_nonneg (transformedFlux chart.graph hg Q Bs hBs k)
      CompactRepresentative v ∧ (∀ k, HasWeakPartial v (C k) k) ∧
        HasDivergenceOn W (fun k => flux A C chart.jump chart.jump_nonneg k-F k) 0 ∧
        (∀ k, CompactRepresentative (F k)) ∧
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ k, k ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 k l) k) ∧
          (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ l, HasWeakPartial (F1 k l) (F2 k t l) t) := by
  filter_upwards [hz,hmode,chart.material] with j hzj hmj hmat
  dsimp only
  let V : Set Space := {x | inverseOriented chart.up chart.axis x ∈ ball (0 : Space) Packet05FixedCollarAtlas.outer.rIn}
  have hmapV : ∀ x ∈ V, inverseOriented chart.up chart.axis x ∈ ball (0 : Space) Packet05FixedCollarAtlas.outer.rIn :=
    fun _ hx => hx
  have hmapW : ∀ x ∈ W, graphMap (liftedHeight chart.graph) x ∈ V :=
    fun x hx => chart.maps_outer x (hW hx)
  exact Packet05ActualHostModeGraph.actual_host_mode_graph (rounded n hn g η hη j) (z j) hzj 1 (u j)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j) hmj chart.body chart.host chart.host_ne
    chart.jump chart.jump_nonneg Packet05FixedCollarAtlas.outer chart.up chart.axis chart.graph
    (chart.regular.of_le (by decide)) V W hmapV hmapW (fun x hx => chart.side x (hW hx))
    (fun x hx => hmat x (hW hx)) Bs hBs hdi hdd A hA

end OQ14.Packet05FixedSubchartEquation
#print axioms OQ14.Packet05FixedSubchartEquation.eventual_actual_subchart_equation

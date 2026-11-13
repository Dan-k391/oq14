import Packet05ActualOrientedGraph
import Packet05PhysicalChartBranches

/-! An actual regular oriented graph yields a bounded open flat chart around
the interface point, with exact physical-side and neighborhood mapping. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualFlatNeighborhood
open Set Filter Metric OQ14.Maxwell OQ14.Packet05ChartOrientationMeasure
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05PhysicalChartBranches
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphChartHomeomorph OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphSmooth
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def chartPoint (up : Bool) (i : Fin 3) (g : Plane → ℝ) (x : Space) : Space :=
  inverseGraphMap (liftedHeight g) (orientedLinear up i x)

theorem chart_point_on_interface (up : Bool) (i : Fin 3) (g : Plane → ℝ) (x : Space)
    (hzero : (orientedLinear up i x) 2 = g (OQ14.ConicalJunctionPhysical.horizontal (orientedLinear up i x))) :
    chartPoint up i g x 2 = 0 := by
  simp [chartPoint,inverseGraphMap,liftedHeight,basis,EuclideanSpace.single_apply,
    PiLp.sub_apply,PiLp.smul_apply,hzero]

theorem actual_flat_neighborhood (body Ω : Set Space) (x : Space) (hΩ : IsOpen Ω) (hxΩ : x ∈ Ω)
    (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 4 g)
    (hzero : (orientedLinear up i x) 2 = g (OQ14.ConicalJunctionPhysical.horizontal (orientedLinear up i x)))
    (hside : ∀ᶠ y in 𝓝 x, y ∈ body ↔
      g (OQ14.ConicalJunctionPhysical.horizontal (orientedLinear up i y)) < (orientedLinear up i y) 2) :
    ∃ r : ℝ, 0 < r ∧ chartPoint up i g x 2 = 0 ∧
      (∀ z ∈ ball (chartPoint up i g x) r,
        inverseOriented up i (graphMap (liftedHeight g) z) ∈ Ω ∧
        (inverseOriented up i (graphMap (liftedHeight g) z) ∈ body ↔ 0 < z 2)) := by
  let c := chartPoint up i g x
  let ψ : Space → Space := fun z => inverseOriented up i (graphMap (liftedHeight g) z)
  have hc : ψ c = x := by
    change inverseOriented up i (graphMap (liftedHeight g)
      (inverseGraphMap (liftedHeight g) (orientedLinear up i x))) = x
    rw [graph_map_right_inverse _ (liftedHeight_normal_invariant g)]
    exact inverse_oriented_left up i x
  have hψ : Continuous ψ := (orientedHomeomorph up i).symm.continuous.comp (graphMap_contDiff g hg).continuous
  have hnear : ∀ᶠ z in 𝓝 c, ψ z ∈ Ω ∧ (ψ z ∈ body ↔ 0 < z 2) := by
    have hΩ' : ∀ᶠ z in 𝓝 c, ψ z ∈ Ω := by
      apply hψ.continuousAt.tendsto.eventually
      simpa [hc] using hΩ.mem_nhds hxΩ
    have hs' : ∀ᶠ z in 𝓝 c, ψ z ∈ body ↔
        g (OQ14.ConicalJunctionPhysical.horizontal (orientedLinear up i (ψ z))) < (orientedLinear up i (ψ z)) 2 := by
      have ht : Tendsto ψ (𝓝 c) (𝓝 (ψ c)) := hψ.continuousAt.tendsto
      rw [hc] at ht
      exact ht.eventually hside
    filter_upwards [hΩ',hs'] with z hz hs
    refine ⟨hz,?_⟩
    have ho : orientedLinear up i (ψ z) = graphMap (liftedHeight g) z := inverse_oriented_right up i _
    rw [hs,ho]
    have hh : OQ14.ConicalJunctionPhysical.horizontal (graphMap (liftedHeight g) z) =
        OQ14.ConicalJunctionPhysical.horizontal z := horizontal_normal_invariant z (liftedHeight g z)
    have hheight := graph_map_height (liftedHeight g) (liftedHeight_normal_invariant g) z
    simp only [liftedHeight,hh] at hheight
    rw [hh]
    constructor <;> intro h <;> linarith
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r,hr,chart_point_on_interface up i g x hzero,?_⟩
  intro z hz
  exact hrsub hz

end OQ14.Packet05ActualFlatNeighborhood
#print axioms OQ14.Packet05ActualFlatNeighborhood.chart_point_on_interface
#print axioms OQ14.Packet05ActualFlatNeighborhood.actual_flat_neighborhood

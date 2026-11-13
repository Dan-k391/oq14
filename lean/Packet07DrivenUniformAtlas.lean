import Packet07DrivenUniformAllCharts
import Packet07DrivenUniformReference

/-! One fixed atlas for every point of the driven family collar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenUniformAtlas
open Set Filter Metric Maxwell Packet07PlanarSetup Packet07DrivenUniformCollarChart
  Packet07DrivenUniformAllCharts Packet05ChartBasis Packet05GraphChartMap
  Packet05PhysicalGraphChart Packet05PhysicalChartBranches
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

def outer {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ} (g : Setup N P d t) : ContDiffBump (0 : Space) :=
  ⟨g.enclosing+1,g.enclosing+2,by linarith [g.enclosing_nonnegative],by linarith⟩

theorem actual_fixed_collar_atlas {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N P d t) (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∃ j0 : ℕ, (∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.centers i‖ → ‖x-g.centers i‖ < b →
        (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔
         x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0)) ∧
      ∀ (i : Fin N) (x : Space), x ∈ annulus g i r b →
      ∃ (up : Bool) (axis : Fin 3) (G : Plane → ℝ) (T bodyChart : Set Space) (host : ℂ) (jump : ℝ),
        ContDiff ℝ 4 G ∧ HasCompactSupport G ∧ IsOpen T ∧ physicalFlatMap up axis G x ∈ T ∧
        host ≠ 0 ∧ 0 ≤ jump ∧
        (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ ball (0 : Space) (outer g).rIn) ∧
        (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart ↔ 0 < y 2) ∧
        ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
          Packet06MaxwellScalarEquation.epsilon (g.rounded j)
            (inverseOriented up axis (graphMap (liftedHeight G) y)) =
            host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart
              then (1+jump : ℂ) else 1) := by
  obtain ⟨j0,hcert,hstable⟩ := Packet07DrivenUniformReference.fixed_reference g r b hr hb
  refine ⟨j0,hstable,?_⟩
  intro i x hx
  have hxout : x ∈ closedBall (g.centers i) g.datum.cutoff.rOut := by
    simp only [mem_closedBall,dist_eq_norm]
    exact hx.2.le.trans (hb.le.trans g.radius_out)
  have hxball : x ∈ closedBall (0 : Space) g.enclosing := g.outer_enclosed i hxout
  have hxouter : x ∈ ball (0 : Space) (outer g).rIn := by
    apply closedBall_subset_ball (show g.enclosing < (outer g).rIn by dsimp [outer]; linarith) hxball
  exact fixed_chart_at_point g r b j0 hstable hcert i x hx (outer g) hxouter
end OQ14.Packet07DrivenUniformAtlas
#print axioms OQ14.Packet07DrivenUniformAtlas.actual_fixed_collar_atlas

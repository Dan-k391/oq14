import Packet05FixedCollarAllCharts

/-! A single smooth reference and one common outer localization produce fixed
material charts at every point of every prescribed modal annulus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05FixedCollarAtlas
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05FixedCollarChart
  Packet05FixedCollarAllCharts Packet05ChartBasis Packet05GraphChartMap
  Packet05PhysicalGraphChart Packet05PhysicalChartBranches
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

def outer : ContDiffBump (0 : Space) := ⟨2,3,by norm_num,by norm_num⟩

theorem actual_fixed_collar_atlas {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∃ j0 : ℕ, (∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.center i‖ → ‖x-g.center i‖ < b → (x ∈ body g j ↔ x ∈ body g j0)) ∧
      ∀ (i : Fin N) (x : Space), x ∈ annulus g i r b →
      ∃ (up : Bool) (axis : Fin 3) (G : Plane → ℝ) (T bodyChart : Set Space) (host : ℂ) (d : ℝ),
        ContDiff ℝ 4 G ∧ HasCompactSupport G ∧ IsOpen T ∧ physicalFlatMap up axis G x ∈ T ∧
        host ≠ 0 ∧ 0 ≤ d ∧
        (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ ball (0 : Space) outer.rIn) ∧
        (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart ↔ 0 < y 2) ∧
        ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
          Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j)
            (inverseOriented up axis (graphMap (liftedHeight G) y)) =
            host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart
              then (1+d : ℂ) else 1) := by
  obtain ⟨j0,hcert,hstable⟩ := Packet05FixedCollarReference.fixed_reference_body n hn g r b hr hb
  refine ⟨j0,hstable,?_⟩
  intro i x hx
  have hxout : x ∈ closedBall (g.center i) g.datum.cutoff.rOut := by
    simp only [mem_closedBall,dist_eq_norm]
    exact hx.2.le.trans (hb.le.trans g.radius_outer)
  have hxball : x ∈ ball (0 : Space) 1 := g.outer_inside i hxout
  have hxouter : x ∈ ball (0 : Space) outer.rIn := by
    have h := ball_subset_ball (show (1 : ℝ) ≤ 2 by norm_num) hxball
    exact h
  exact fixed_chart_at_point n hn g η hη r b hb j0 hstable hcert i x hx outer hxouter

end OQ14.Packet05FixedCollarAtlas
#print axioms OQ14.Packet05FixedCollarAtlas.actual_fixed_collar_atlas

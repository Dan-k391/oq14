import Packet05FixedCollarReference
import Packet05ActualFlatNeighborhood
import Packet06MaxwellScalarEquation

/-! A single actual reference-body chart and exact binary material law work
on a fixed open annulus for every sufficiently late rounded mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05FixedCollarChart
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05ActualOrientedGraph
  Packet05ActualFlatNeighborhood Packet05ChartBasis Packet05GraphChartMap Packet05PhysicalGraphChart
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

def annulus {N : ℕ} {n : ℝ} (g : Packet06ConcreteModalGeometry.Geometry N n)
    (i : Fin N) (r b : ℝ) : Set Space := {x | r < ‖x-g.center i‖ ∧ ‖x-g.center i‖ < b}

theorem annulus_open {N : ℕ} {n : ℝ} (g : Packet06ConcreteModalGeometry.Geometry N n)
    (i : Fin N) (r b : ℝ) : IsOpen (annulus g i r b) := by
  exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

theorem fixed_collar_chart {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (r b : ℝ) (hb : b < g.radius) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.center i‖ → ‖x-g.center i‖ < b → (x ∈ body g j ↔ x ∈ body g j0))
    (i : Fin N) (x : Space) (hx : x ∈ annulus g i r b) (hfront : x ∈ frontier (body g j0))
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ body g j0 ↔ 0 < F y))
    (χ : ContDiffBump (0 : Space)) (hxχ : x ∈ ball (0 : Space) χ.rIn) :
    ∃ (up : Bool) (axis : Fin 3) (G : Plane → ℝ) (T : Set Space),
      ContDiff ℝ 4 G ∧ HasCompactSupport G ∧ IsOpen T ∧ chartPoint up axis G x ∈ T ∧
      chartPoint up axis G x 2 = 0 ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ ball (0 : Space) χ.rIn) ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ body g j0 ↔ 0 < y 2) ∧
      ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
        Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j)
          (inverseOriented up axis (graphMap (liftedHeight G) y)) =
          (n^2 : ℂ)*(by classical exact if inverseOriented up axis (graphMap (liftedHeight G) y) ∈ body g j0
            then (1+η : ℂ) else 1) := by
  classical
  obtain ⟨up,axis,G,hG,hGc,hzero,hside⟩ := actual_oriented_graph (body g j0) x hfront hcert
  let Ω : Set Space := annulus g i r b ∩ ball (0 : Space) χ.rIn
  have hΩ : IsOpen Ω := (annulus_open g i r b).inter isOpen_ball
  obtain ⟨δ,hδ,hpoint,hflat⟩ := actual_flat_neighborhood (body g j0) Ω x hΩ ⟨hx,hxχ⟩ up axis G hG hzero hside
  let T := ball (chartPoint up axis G x) δ
  refine ⟨up,axis,G,T,hG,hGc,isOpen_ball,mem_ball_self hδ,hpoint,?_,?_,?_⟩
  · intro y hy
    exact (hflat y hy).1.2
  · intro y hy
    exact (hflat y hy).2
  · filter_upwards [hstable] with j hj y hy
    let z := inverseOriented up axis (graphMap (liftedHeight G) y)
    have hz := (hflat y hy).1.1
    have hzb : z ∈ ball (0 : Space) 1 := by
      apply g.outer_inside i
      change z ∈ closedBall (g.center i) g.datum.cutoff.rOut
      simp only [mem_closedBall,dist_eq_norm]
      exact hz.2.le.trans (hb.le.trans g.radius_outer)
    have hnz : ‖z‖ < 1 := by simpa using hzb
    have hs := hj i z hz.1 hz.2
    have he := dielectric_values n hn g η hη j z
    change Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j) z =
      (n^2 : ℂ)*(if z ∈ body g j0 then (1+η : ℂ) else 1)
    unfold Packet06MaxwellScalarEquation.epsilon
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, he]
    by_cases hbody : z ∈ body g j0
    · have hjbody : z ∈ body g j := hs.mpr hbody
      simp [hbody,hjbody,hnz]; ring
    · have hjbody : z ∉ body g j := fun h => hbody (hs.mp h)
      simp [hbody,hjbody,hnz]

end OQ14.Packet05FixedCollarChart
#print axioms OQ14.Packet05FixedCollarChart.annulus_open
#print axioms OQ14.Packet05FixedCollarChart.fixed_collar_chart

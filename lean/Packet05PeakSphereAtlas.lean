import Packet05FiniteFixedAtlas

/-! The physical sphere surrounding a cone tip has a finite fixed material
atlas lying strictly inside its cone radius. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PeakSphereAtlas
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05FixedCollarChart
  Packet05FiniteFixedAtlas Packet05ChartBasis Packet05GraphChartMap Packet05PhysicalGraphChart
open scoped Topology
abbrev Space := Maxwell.Space

theorem peak_sphere_atlas {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (i : Fin N) (R : ℝ) (hR : 0 < R) (hRradius : R < g.radius) :
    ∃ j0 : ℕ, ∃ J : Finset (Chart n hn g η hη),
      (∀ᶠ j : ℕ in atTop, ∀ (k : Fin N) (x : Space),
        R/2 < ‖x-g.center k‖ → ‖x-g.center k‖ < (R+g.radius)/2 →
          (x ∈ body g j ↔ x ∈ body g j0)) ∧
      sphere (g.center i) R ⊆ ⋃ c ∈ J, physical c ∧
      (∀ c ∈ J, IsOpen (physical c)) ∧
      ∀ᶠ j : ℕ in atTop, ∀ c ∈ J, ∀ y ∈ c.flat,
        Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j)
          (inverseOriented c.up c.axis (graphMap (liftedHeight c.graph) y)) =
          c.host * (by classical exact if inverseOriented c.up c.axis (graphMap (liftedHeight c.graph) y) ∈ c.body
            then (1+c.jump : ℂ) else 1) := by
  apply finite_fixed_atlas n hn g η hη (R/2) ((R+g.radius)/2) (by linarith) (by linarith) i
    (sphere (g.center i) R) (isCompact_sphere (g.center i) R)
  intro x hx
  have hdist : ‖x-g.center i‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hx
  change R/2 < ‖x-g.center i‖ ∧ ‖x-g.center i‖ < (R+g.radius)/2
  rw [hdist]
  constructor <;> linarith

end OQ14.Packet05PeakSphereAtlas
#print axioms OQ14.Packet05PeakSphereAtlas.peak_sphere_atlas

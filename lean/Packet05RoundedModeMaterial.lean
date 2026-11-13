import Packet05ActualBoundaryMode
import Packet06ConcreteModalRounding

/-! Actual rounded modal material has the required positive host law near each
interior cone interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RoundedModeMaterial
open Set Filter Metric Maxwell Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem local_cone_material {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (j : ℕ) (x : Space) (hx : x ∈ ball (0 : Space) 1) :
    ∀ᶠ y in 𝓝 x, Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j) y =
      (n^2 : ℂ) * (by classical exact if y ∈ body g j then (1+η : ℂ) else 1) := by
  classical
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have hv := dielectric_values n hn g η hη j y
  have hy' : ‖y‖ < 1 := by simpa using hy
  unfold Packet06MaxwellScalarEquation.epsilon
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, hv]
  by_cases h : y ∈ body g j
  · simp [h,hy']; ring
  · simp [h,hy']


theorem boundary_inside_sphere {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) (j : ℕ) (x : Space)
    (hx : x ∈ frontier (body g j)) : x ∈ ball (0 : Space) 1 := by
  obtain ⟨i,hi⟩ := CommonBinaryInterface.frontier_body_component
    (fun _ => g.datum) (fun _ => g.radius) g.center j x hx
  apply g.outer_inside i
  exact CommonBinaryInterface.closure_component_subset
    (fun _ => g.datum) (fun _ => g.radius) g.center
    (fun _ => g.radius_pos) (fun _ => g.radius_outer) j i (frontier_subset_closure hi)

theorem eventually_boundary_certificate {N : ℕ} {n : ℝ}
    (g : Packet06ConcreteModalGeometry.Geometry N n) :
    ∀ᶠ j : ℕ in atTop, ∀ x ∈ frontier (body g j),
      ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
        fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ U, (y ∈ body g j ↔ 0 < F y) := by
  exact CommonBinaryInterface.eventually_body_smooth
    (fun _ => g.datum) (fun _ => g.radius) g.center
    (fun _ => g.radius_pos) (fun _ => g.radius_outer) g.outer_disjoint
end OQ14.Packet05RoundedModeMaterial
#print axioms OQ14.Packet05RoundedModeMaterial.local_cone_material
#print axioms OQ14.Packet05RoundedModeMaterial.boundary_inside_sphere
#print axioms OQ14.Packet05RoundedModeMaterial.eventually_boundary_certificate

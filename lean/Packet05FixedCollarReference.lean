import Packet05RoundedFixedCollar
import Packet05RoundedModeMaterial

/-! One actual smooth rounded body serves as a single fixed chart geometry
for every sufficiently late family member on the prescribed annuli. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05FixedCollarReference
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05RoundedFixedCollar
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_reference_body {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∃ j0 : ℕ,
      (∀ x ∈ frontier (body g j0), ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
        fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
          ∀ y ∈ U, (y ∈ body g j0 ↔ 0 < F y)) ∧
      ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
        r < ‖x-g.center i‖ → ‖x-g.center i‖ < b →
        (x ∈ body g j ↔ x ∈ body g j0) := by
  have hbody := eventually_body_annulus n hn g r b hr hb
  have hcert := Packet05RoundedModeMaterial.eventually_boundary_certificate g
  obtain ⟨j0,hj0,hcert0⟩ := (hbody.and hcert).exists
  refine ⟨j0,hcert0,?_⟩
  filter_upwards [hbody] with j hj i x hl hh
  exact (hj i x hl.le hh.le).trans (hj0 i x hl.le hh.le).symm

end OQ14.Packet05FixedCollarReference
#print axioms OQ14.Packet05FixedCollarReference.fixed_reference_body

import Packet05FixedCollarChart

/-! On any fixed open phase neighborhood in the annulus, every late rounded
family member has the same constant dielectric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FixedCollarHomogeneous
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05FixedCollarChart
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_constant_on_phase {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (r b : ℝ) (hb : b < g.radius) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.center i‖ → ‖x-g.center i‖ < b → (x ∈ body g j ↔ x ∈ body g j0))
    (i : Fin N) (Ω : Set Space) (hΩ : Ω ⊆ annulus g i r b) (inside : Prop)
    (hphase : ∀ x ∈ Ω, x ∈ body g j0 ↔ inside) :
    ∀ᶠ j : ℕ in atTop, ∀ x ∈ Ω,
      Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j) x =
        (n^2 : ℂ)*(by classical exact if inside then (1+η : ℂ) else 1) := by
  classical
  filter_upwards [hstable] with j hj x hx
  have hxann := hΩ hx
  have hxout : x ∈ closedBall (g.center i) g.datum.cutoff.rOut := by
    simp only [mem_closedBall,dist_eq_norm]
    exact hxann.2.le.trans (hb.le.trans g.radius_outer)
  have hxnorm : ‖x‖ < 1 := by simpa using g.outer_inside i hxout
  have hs := (hj i x hxann.1 hxann.2).trans (hphase x hx)
  have he := dielectric_values n hn g η hη j x
  unfold Packet06MaxwellScalarEquation.epsilon
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, he]
  by_cases hp : inside
  · have hbody := hs.mpr hp
    simp [hp,hbody,hxnorm]; ring
  · have hbody : x ∉ body g j := fun h => hp (hs.mp h)
    simp [hp,hbody,hxnorm]

end OQ14.Packet05FixedCollarHomogeneous
#print axioms OQ14.Packet05FixedCollarHomogeneous.eventually_constant_on_phase

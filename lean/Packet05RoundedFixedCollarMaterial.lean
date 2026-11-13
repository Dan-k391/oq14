import Packet05RoundedFixedCollar
import Packet06MaxwellScalarEquation

/-! The actual rounded modal dielectric is a single fixed sharp-cone binary
coefficient on the whole fixed open annulus, eventually in the family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RoundedFixedCollarMaterial
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05RoundedFixedCollar
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_fixed_annulus_material {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.center i‖ → ‖x-g.center i‖ < b →
      Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j) x =
        (n^2 : ℂ)*(by classical exact if ConicalJunctionPhysical.split (x-g.center i) ∈
          ConicalSmoothCapGraph.sharpCone (ConicalJunctionPhysical.slope g.datum.threshold)
          then (1+η : ℂ) else 1) := by
  classical
  filter_upwards [eventually_body_annulus n hn g r b hr hb] with j hj i x hl hh
  have hxout : x ∈ closedBall (g.center i) g.datum.cutoff.rOut := by
    simp only [mem_closedBall,dist_eq_norm]
    exact hh.le.trans (hb.le.trans g.radius_outer)
  have hxball := g.outer_inside i hxout
  have hxnorm : ‖x‖ < 1 := by simpa using hxball
  have he := dielectric_values n hn g η hη j x
  have hs := hj i x hl.le hh.le
  unfold Packet06MaxwellScalarEquation.epsilon
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, he]
  by_cases hc : ConicalJunctionPhysical.split (x-g.center i) ∈
      ConicalSmoothCapGraph.sharpCone (ConicalJunctionPhysical.slope g.datum.threshold)
  · have hbody : x ∈ body g j := hs.mpr hc
    simp [hc,hbody,hxnorm]; ring
  · have hbody : x ∉ body g j := fun h => hc (hs.mp h)
    simp [hc,hbody,hxnorm]

end OQ14.Packet05RoundedFixedCollarMaterial
#print axioms OQ14.Packet05RoundedFixedCollarMaterial.eventually_fixed_annulus_material

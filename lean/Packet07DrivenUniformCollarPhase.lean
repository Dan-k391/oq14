import Packet07DrivenUniformCollarChart

/-! On any fixed open phase neighborhood in the annulus, every late rounded
family member has the same constant dielectric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet07DrivenUniformCollarPhase
open Set Filter Metric Maxwell Packet07PlanarSetup Packet07DrivenUniformCollarChart
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_constant_on_phase {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ} (g : Setup N P d t)
    (r b : ℝ) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.centers i‖ → ‖x-g.centers i‖ < b → (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔ x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0))
    (i : Fin N) (Ω : Set Space) (hΩ : Ω ⊆ annulus g i r b) (inside : Prop)
    (hphase : ∀ x ∈ Ω, x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 ↔ inside) :
    ∀ᶠ j : ℕ in atTop, ∀ x ∈ Ω,
      Packet06MaxwellScalarEquation.epsilon (g.rounded j) x =
        (1 : ℂ)*(by classical exact if inside then (1+d : ℂ) else 1) := by
  classical
  filter_upwards [hstable] with j hj x hx
  have hxann := hΩ hx
  have hs := (hj i x hxann.1 hxann.2).trans (hphase x hx)
  have he := CommonBinaryInterface.coefficient_body g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_pos g.radii_outer g.outer_sep d
    (fun _ => g.contrast_eq) j x
  change (g.rounded j).value (VectorFourier.coordinateMap x) =
    (if x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j then d else 0) at he
  unfold Packet06MaxwellScalarEquation.epsilon
  rw [he]
  by_cases hp : inside
  · have hbody := hs.mpr hp
    simp [hp,hbody]
  · have hbody : x ∉ CommonBinaryInterface.body g.dataFamily g.radii g.centers j := fun h => hp (hs.mp h)
    simp [hp,hbody]

end OQ14.Packet07DrivenUniformCollarPhase
#print axioms OQ14.Packet07DrivenUniformCollarPhase.eventually_constant_on_phase

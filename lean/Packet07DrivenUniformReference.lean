import Packet07DrivenUniformGraph
import CommonBinaryInterface

/-! A fixed smooth reference body for the literal driven rounding family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet07DrivenUniformReference
open MeasureTheory Set Metric Filter Maxwell
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_reference {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (r b : ℝ) (hr : 0 < r) (hb : b < g.radius) :
    ∃ j0 : ℕ,
      (∀ x ∈ frontier (CommonBinaryInterface.body g.dataFamily g.radii g.centers j0),
        ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
          ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
            (y ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 ↔ 0 < F y)) ∧
      ∀ᶠ j : ℕ in atTop, ∀ i x, r < ‖x-g.centers i‖ → ‖x-g.centers i‖ < b →
        (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔
         x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0) := by
  classical
  have ha := CommonBinaryCollar.eventually_annuli_agree g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_outer g.outer_sep g.radii_pos
    (fun _ => r) (fun _ => b) (fun _ => hr) (fun _ => hb)
  have hs := CommonBinaryInterface.eventually_body_smooth g.dataFamily g.radii g.centers
    g.radii_pos g.radii_outer g.outer_sep
  obtain ⟨j0,hj0,hs0⟩ := (ha.and hs).exists
  refine ⟨j0,hs0,?_⟩
  filter_upwards [ha] with j hj i x hlow hhigh
  have hv := (hj i x hlow.le hhigh.le).trans (hj0 i x hlow.le hhigh.le).symm
  have hbody (n : ℕ) := CommonBinaryInterface.coefficient_body g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_pos g.radii_outer g.outer_sep d
    (fun i => g.contrast_eq) n x
  rw [hbody j,hbody j0] at hv
  by_cases h1 : x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j
  · by_cases h2 : x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0
    · exact iff_of_true h1 h2
    · simp only [h1,h2,if_true,if_false] at hv
      exact False.elim (g.contrast_pos.ne' hv)
  · by_cases h2 : x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0
    · simp only [h1,h2,if_true,if_false] at hv
      exact False.elim (g.contrast_pos.ne' hv.symm)
    · exact iff_of_false h1 h2
end OQ14.Packet07DrivenUniformReference
#print axioms OQ14.Packet07DrivenUniformReference.fixed_reference

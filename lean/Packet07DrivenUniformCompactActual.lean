import Packet07DrivenUniformCompactBinary
import CommonBinaryInterface

/-! Actual compact phase branches for every late rounded driven device. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenUniformCompactActual
open MeasureTheory Set Filter Metric Maxwell Packet05BoundaryMaterialMode
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem eventually_compact_branches {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (k : ℝ) (hk0 : k ≠ 0) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) :
    ∀ᶠ j : ℕ in atTop, ∀ (K : Set Space), IsCompact K →
      let body := CommonBinaryInterface.body g.dataFamily g.radii g.centers j
      ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
        (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
        (∀ i, (fun y => g.electric k j input y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
        (∀ i, (fun y => g.electric k j input y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) := by
  classical
  filter_upwards [CommonBinaryInterface.eventually_body_smooth g.dataFamily g.radii g.centers
    g.radii_pos g.radii_outer g.outer_sep] with j hcert K hK
  dsimp only
  let body := CommonBinaryInterface.body g.dataFamily g.radii g.centers j
  have hbody : IsOpen body := CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j
  have he (x : Space) : Packet06MaxwellScalarEquation.epsilon (g.rounded j) x =
      (1 : ℂ)*(if x ∈ body then (1+d : ℂ) else 1) := by
    have h := CommonBinaryInterface.coefficient_body g.dataFamily g.radii g.centers d
      g.contrast_pos.le g.contrast_bound g.radii_pos g.radii_outer g.outer_sep d
      (fun _ => g.contrast_eq) j x
    change (g.rounded j).value (VectorFourier.coordinateMap x) = (if x ∈ body then d else 0) at h
    unfold Packet06MaxwellScalarEquation.epsilon
    rw [h]
    split_ifs <;> simp
  have hval : (1+d : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+d by linarith [g.contrast_pos]))
  apply Packet07DrivenUniformCompactBinary.compact_binary_driven g k hk0 input hk j K univ body hK
    isOpen_univ hbody (subset_univ K) (1+d : ℂ) 1 hval one_ne_zero
  · intro x hx
    simpa only [if_pos hx.2,one_mul] using he x
  · intro x hx
    simpa only [if_neg hx.2,one_mul] using he x
  · intro x hx
    exact Packet07DrivenUniformBoundaryMaterial.boundary_material_driven g k hk0 input hk j body x hx.2
      (hcert x hx.2) 1 one_ne_zero d g.contrast_pos.le (Filter.Eventually.of_forall he)
end OQ14.Packet07DrivenUniformCompactActual
#print axioms OQ14.Packet07DrivenUniformCompactActual.eventually_compact_branches

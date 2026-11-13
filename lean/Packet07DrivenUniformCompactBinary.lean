import Packet07DrivenUniformCompactPhase
import Packet07DrivenUniformBoundaryMaterial

/-! Two actual constant material phases and their genuine interface traces
give continuous mode branches on both compact phase closures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet07DrivenUniformCompactBinary
open MeasureTheory Metric Set Maxwell Packet05BoundaryMaterialMode

theorem compact_binary_driven
    {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {contrast threshold : ℝ}
    (setup : Packet07PlanarSetup.Setup N Pset contrast threshold) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius contrast setup.enclosing) (j0 : ℕ)
    (K Ω body : Set Space) (hK : IsCompact K) (hΩ : IsOpen Ω) (hbody : IsOpen body) (hKΩ : K ⊆ Ω)
    (insideValue outsideValue : ℂ) (hi : insideValue ≠ 0) (ho : outsideValue ≠ 0)
    (hin : ∀ x ∈ Ω ∩ body, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) x=insideValue)
    (hout : ∀ x ∈ Ω ∩ bodyᶜ, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) x=outsideValue)
    (hboundary : ∀ x ∈ Ω ∩ frontier body, HasPhaseRepresentatives
      (setup.electric k j0 input) body x) :
    let E := setup.electric k j0 input
    ∃ inside outside : Fin 3 → Space → ℂ,
      (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
      (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
      (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
      (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) := by
  dsimp only
  have hbin : ∀ x ∈ Ω ∩ frontier body, ∃ (O : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ (∀ i, Continuous (reps i)) ∧
      ∀ i, (fun y => setup.electric k j0 input y i) =ᵐ[volume.restrict (O ∩ body)] reps i := by
    intro x hx
    obtain ⟨O,reps,out,hO,hxO,hr,_,hae,_⟩ := hboundary x hx
    exact ⟨O,reps,hO,hxO,hr,hae⟩
  obtain ⟨inside,hic,hiae⟩ := Packet07DrivenUniformCompactPhase.compact_driven_phase setup k hk0 input hk j0
    K Ω body hK hΩ hbody hKΩ insideValue hi hin hbin
  have hsub : (closure body)ᶜ ⊆ bodyᶜ := fun _ hx hb => hx (subset_closure hb)
  have hbout : ∀ x ∈ Ω ∩ frontier (closure body)ᶜ, ∃ (O : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ (∀ i, Continuous (reps i)) ∧
      ∀ i, (fun y => setup.electric k j0 input y i) =ᵐ[volume.restrict (O ∩ (closure body)ᶜ)] reps i := by
    intro x hx
    have hxfront : x ∈ frontier body := frontier_closure_subset (by simpa only [frontier_compl] using hx.2)
    obtain ⟨O,ins,reps,hO,hxO,_,hr,_,hae⟩ := hboundary x ⟨hx.1,hxfront⟩
    refine ⟨O,reps,hO,hxO,hr,?_⟩
    intro i
    exact ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right O hsub) (hae i)
  obtain ⟨outside,hoc,hoae⟩ := Packet07DrivenUniformCompactPhase.compact_driven_phase setup k hk0 input hk j0
    K Ω (closure body)ᶜ hK hΩ isClosed_closure.isOpen_compl hKΩ outsideValue ho
    (fun x hx => hout x ⟨hx.1,hsub hx.2⟩) hbout
  exact ⟨inside,outside,hic,hoc,hiae,hoae⟩

end OQ14.Packet07DrivenUniformCompactBinary
#print axioms OQ14.Packet07DrivenUniformCompactBinary.compact_binary_driven

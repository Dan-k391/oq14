import Packet05PhaseGluing

/-! Local actual field representatives near a compact phase closure produce
one continuous branch there, retaining equality on the actual open phase. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05CompactPhaseRepresentative
open MeasureTheory Set Maxwell Packet05PhaseGluing

theorem compact_phase_representative (K U : Set Space) (hK : IsCompact K) (hU : IsOpen U)
    (E : Space → ℂ)
    (hlocal : ∀ x ∈ K ∩ closure U, ∃ (O : Set Space) (f : Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ Continuous f ∧ f =ᵐ[volume.restrict (U ∩ O)] E) :
    ∃ F : Space → ℂ, ContinuousOn F (K ∩ closure U) ∧
      F =ᵐ[volume.restrict (K ∩ U)] E := by
  classical
  let Index := {x : Space // x ∈ K ∩ closure U}
  choose O f hO hxO hf hae using fun x : Index => hlocal x x.property
  have hcover : K ∩ closure U ⊆ ⋃ x : Index, O x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxO ⟨x,hx⟩⟩
  obtain ⟨t,ht⟩ := (hK.inter_right isClosed_closure).elim_finite_subcover O hO hcover
  let V : Set Space := ⋃ j : t, O j
  have hKV : K ∩ closure U ⊆ V := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩
  obtain ⟨F,hF,hagree,hAE⟩ := finite_phase_gluing U hU (fun j : t => O j)
    (fun j => hO j) E (fun j => f j) (fun j => hf j) (fun j => hae j)
  refine ⟨F,hF.mono (fun x hx => ⟨hx.2,hKV hx⟩),?_⟩
  have hsub : K ∩ U ⊆ U ∩ V := fun x hx => ⟨hx.2,hKV ⟨hx.1,subset_closure hx.2⟩⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub hAE

end OQ14.Packet05CompactPhaseRepresentative
#print axioms OQ14.Packet05CompactPhaseRepresentative.compact_phase_representative

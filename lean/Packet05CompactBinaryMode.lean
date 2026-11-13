import Packet05CompactModePhase
import Packet05BoundaryMaterialMode

/-! Two actual constant material phases and their genuine interface traces
give continuous mode branches on both compact phase closures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05CompactBinaryMode
open MeasureTheory Metric Set Maxwell Packet05BoundaryMaterialMode

theorem compact_binary_mode
    (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0) (Rsource : ℝ)
    (mode : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 Rsource → c.value (VectorFourier.coordinateMap x)=0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock c z Rsource mode=0)
    (K Ω body : Set Space) (hK : IsCompact K) (hΩ : IsOpen Ω) (hbody : IsOpen body) (hKΩ : K ⊆ Ω)
    (insideValue outsideValue : ℂ) (hi : insideValue ≠ 0) (ho : outsideValue ≠ 0)
    (hin : ∀ x ∈ Ω ∩ body, Packet06MaxwellScalarEquation.epsilon c x=insideValue)
    (hout : ∀ x ∈ Ω ∩ bodyᶜ, Packet06MaxwellScalarEquation.epsilon c x=outsideValue)
    (hboundary : ∀ x ∈ Ω ∩ frontier body, HasPhaseRepresentatives
      (Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)) body x) :
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)
    ∃ inside outside : Fin 3 → Space → ℂ,
      (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
      (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
      (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
      (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) := by
  dsimp only
  have hbin : ∀ x ∈ Ω ∩ frontier body, ∃ (O : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ (∀ i, Continuous (reps i)) ∧
      ∀ i, (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode)
        (DynamicVolume.source c mode) y i) =ᵐ[volume.restrict (O ∩ body)] reps i := by
    intro x hx
    obtain ⟨O,reps,out,hO,hxO,hr,_,hae,_⟩ := hboundary x hx
    exact ⟨O,reps,hO,hxO,hr,hae⟩
  obtain ⟨inside,hic,hiae⟩ := Packet05CompactModePhase.compact_mode_phase c z hz Rsource mode hc hmode
    K Ω body hK hΩ hbody hKΩ insideValue hi hin hbin
  have hsub : (closure body)ᶜ ⊆ bodyᶜ := fun _ hx hb => hx (subset_closure hb)
  have hbout : ∀ x ∈ Ω ∩ frontier (closure body)ᶜ, ∃ (O : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ (∀ i, Continuous (reps i)) ∧
      ∀ i, (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode)
        (DynamicVolume.source c mode) y i) =ᵐ[volume.restrict (O ∩ (closure body)ᶜ)] reps i := by
    intro x hx
    have hxfront : x ∈ frontier body := frontier_closure_subset (by simpa only [frontier_compl] using hx.2)
    obtain ⟨O,ins,reps,hO,hxO,_,hr,_,hae⟩ := hboundary x ⟨hx.1,hxfront⟩
    refine ⟨O,reps,hO,hxO,hr,?_⟩
    intro i
    exact ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_right O hsub) (hae i)
  obtain ⟨outside,hoc,hoae⟩ := Packet05CompactModePhase.compact_mode_phase c z hz Rsource mode hc hmode
    K Ω (closure body)ᶜ hK hΩ isClosed_closure.isOpen_compl hKΩ outsideValue ho
    (fun x hx => hout x ⟨hx.1,hsub hx.2⟩) hbout
  exact ⟨inside,outside,hic,hoc,hiae,hoae⟩

end OQ14.Packet05CompactBinaryMode
#print axioms OQ14.Packet05CompactBinaryMode.compact_binary_mode

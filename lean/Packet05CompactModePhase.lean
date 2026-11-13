import Packet05CompactPhaseRepresentative
import Packet05HomogeneousActualMode

/-! Actual interior mode regularity and actual boundary phase representatives
give an attained-maximum-ready branch on any compact phase closure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05CompactModePhase
open MeasureTheory Metric Set Maxwell

theorem compact_mode_phase
    (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0) (Rsource : ℝ)
    (mode : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 Rsource → c.value (VectorFourier.coordinateMap x)=0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock c z Rsource mode=0)
    (K Ω U : Set Space) (hK : IsCompact K) (hΩ : IsOpen Ω) (hU : IsOpen U) (hKΩ : K ⊆ Ω)
    (host : ℂ) (hhost : host ≠ 0)
    (hmaterial : ∀ x ∈ Ω ∩ U, Packet06MaxwellScalarEquation.epsilon c x=host)
    (hboundary : ∀ x ∈ Ω ∩ frontier U, ∃ (O : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen O ∧ x ∈ O ∧ (∀ i, Continuous (reps i)) ∧
      ∀ i, (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode)
        (DynamicVolume.source c mode) y i) =ᵐ[volume.restrict (O ∩ U)] reps i) :
    ∃ reps : Fin 3 → Space → ℂ,
      (∀ i, ContinuousOn (reps i) (K ∩ closure U)) ∧
      ∀ i, (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode)
        (DynamicVolume.source c mode) y i) =ᵐ[volume.restrict (K ∩ U)] reps i := by
  classical
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)
  have hlocal (i : Fin 3) (x : Space) (hx : x ∈ K ∩ closure U) :
      ∃ (O : Set Space) (f : Space → ℂ), IsOpen O ∧ x ∈ O ∧ Continuous f ∧
        f =ᵐ[volume.restrict (U ∩ O)] (fun y => E y i) := by
    by_cases hxU : x ∈ U
    · obtain ⟨O,reps,hO,hxO,hOsub,hr,hae⟩ :=
        Packet05HomogeneousActualMode.actual_homogeneous_neighborhood c z hz Rsource mode hc hmode
          (Ω ∩ U) (hΩ.inter hU) x ⟨hKΩ hx.1,hxU⟩ host hhost hmaterial
      refine ⟨O,reps i,hO,hxO,hr i,?_⟩
      have hh : (fun y => E y i) =ᵐ[volume.restrict O] reps i := hae i
      exact ae_restrict_of_ae_restrict_of_subset inter_subset_right hh.symm
    · have hxfront : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx.2,hxU⟩
      obtain ⟨O,reps,hO,hxO,hr,hae⟩ := hboundary x ⟨hKΩ hx.1,hxfront⟩
      refine ⟨O,reps i,hO,hxO,hr i,?_⟩
      have hh : (fun y => E y i) =ᵐ[volume.restrict (O ∩ U)] reps i := hae i
      simpa only [inter_comm U O] using hh.symm
  have hex (i : Fin 3) := Packet05CompactPhaseRepresentative.compact_phase_representative
    K U hK hU (fun y => E y i) (hlocal i)
  choose reps hr hae using hex
  exact ⟨reps,hr,fun i => (hae i).symm⟩

end OQ14.Packet05CompactModePhase
#print axioms OQ14.Packet05CompactModePhase.compact_mode_phase

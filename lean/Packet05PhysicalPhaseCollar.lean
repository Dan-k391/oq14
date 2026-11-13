import Packet05PhaseAEBound
import Packet06RoundedBranchSymmetry

/-! A physical a.e. collar bound controls both actual one-sided phase traces
on that open collar, including its material interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PhysicalPhaseCollar
open MeasureTheory Set Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06RoundedBranchSymmetry
abbrev Space := Maxwell.Space

theorem physical_phase_collar (body K A : Set Space) (hb : IsOpen body) (hA : IsOpen A)
    (hAK : A ⊆ K) (E : Field) (inside outside : Fin 3 → Space → ℂ)
    (hin : ∀ i, ContinuousOn (inside i) (K ∩ closure body))
    (hout : ∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ))
    (hiae : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i)
    (hoae : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i)
    (B : ℝ) (hbound : ∀ᵐ x ∂volume.restrict A, physicalAmplitude (fun i y => E y i) x ≤ B) :
    ∀ b x, x ∈ A ∩ phaseDomain body b → physicalAmplitude (phaseField inside outside b) x ≤ B := by
  intro b
  let U := phaseOpen body b
  let R := phaseField inside outside b
  have hopen : IsOpen U := by cases b; exact isClosed_closure.isOpen_compl; exact hb
  have hcont : ∀ i, ContinuousOn (R i) (K ∩ phaseDomain body b) := by
    cases b; exact hout; exact hin
  have hae : ∀ i, (fun x => E x i) =ᵐ[volume.restrict (K ∩ U)] R i := by
    cases b; exact hoae; exact hiae
  have hf : ContinuousOn (physicalAmplitude R) (closure U ∩ A) :=
    (amplitude_continuousOn R _ hcont).mono (fun x hx => ⟨hAK hx.2,(phaseDomain_eq body b).symm ▸ hx.1⟩)
  have hsub : U ∩ A ⊆ K ∩ U := fun x hx => ⟨hAK hx.2,hx.1⟩
  have hfa : physicalAmplitude R =ᵐ[volume.restrict (U ∩ A)] physicalAmplitude (fun i y => E y i) := by
    have hh : ∀ᵐ x ∂volume.restrict (U ∩ A), ∀ i, E x i=R i x :=
      ae_restrict_of_ae_restrict_of_subset hsub (ae_all_iff.mpr hae)
    filter_upwards [hh] with x hx
    simp only [physicalAmplitude]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [hx i])
  intro x hx
  exact Packet05PhaseAEBound.phase_ae_bound U A hopen hA (physicalAmplitude R)
    (physicalAmplitude (fun i y => E y i)) hf B hfa hbound x ⟨(phaseDomain_eq body b) ▸ hx.2,hx.1⟩

end OQ14.Packet05PhysicalPhaseCollar
#print axioms OQ14.Packet05PhysicalPhaseCollar.physical_phase_collar

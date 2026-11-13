import Packet07DrivenCyclicPhaseAE
import Packet06PlacementHomeomorph

/-! Transport actual one-sided branch identities and their whole-collar
pointwise bounds through the normalized physical placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenCyclicTrace
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedKernel
open scoped Topology

theorem cyclic_trace (E : Field)
    (body K A : Set Space) (hb : IsOpen body) (hK : MeasurableSet K)
    (inside outside : Fin 3 → Space → ℂ)
    (hin : ∀ k, ContinuousOn (inside k) (K ∩ closure body))
    (hout : ∀ k, ContinuousOn (outside k) (K ∩ closure (closure body)ᶜ))
    (hiae : ∀ k, (fun x => E x k) =ᵐ[volume.restrict (K ∩ body)] inside k)
    (hoae : ∀ k, (fun x => E x k) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside k)
    (B : ℝ) (hbound : ∀ phase x, x ∈ A ∩ phaseDomain body phase →
      physicalAmplitude (phaseField inside outside phase) x ≤ B)
    :
    let h := placement 1 (by norm_num) 0
    (∀ k, ContinuousOn (transport 1 (by norm_num) 0 inside k) (h '' K ∩ closure (h '' body))) ∧
    (∀ k, ContinuousOn (transport 1 (by norm_num) 0 outside k) (h '' K ∩ closure (closure (h '' body))ᶜ)) ∧
    (∀ k, (fun y => Packet06CyclicRotationMaxwell.rotateField E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body)] transport 1 (by norm_num) 0 inside k) ∧
    (∀ k, (fun y => Packet06CyclicRotationMaxwell.rotateField E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body))ᶜ)] transport 1 (by norm_num) 0 outside k) ∧
    ∀ phase y, y ∈ h '' A ∩ phaseDomain (h '' body) phase →
      physicalAmplitude (phaseField (transport 1 (by norm_num) 0 inside) (transport 1 (by norm_num) 0 outside) phase) y ≤ B := by
  dsimp only
  let h := placement 1 (by norm_num) 0
  have hi : h '' (K ∩ closure body) = h '' K ∩ closure (h '' body) := by
    rw [Set.image_inter h.injective,h.image_closure]
  have ho : h '' (K ∩ closure (closure body)ᶜ) = h '' K ∩ closure (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_closure,h.image_compl,h.image_closure]
  have hei : h '' (K ∩ body) = h '' K ∩ h '' body := by
    rw [Set.image_inter h.injective]
  have heo : h '' (K ∩ (closure body)ᶜ) = h '' K ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_compl,h.image_closure]
  have hei' := hei
  have heo' := heo
  dsimp only [h] at hei' heo'
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k
    rw [← hi]
    exact continuous_transport 1 (by norm_num) 0 inside _ hin k
  · intro k
    rw [← ho]
    exact continuous_transport 1 (by norm_num) 0 outside _ hout k
  · intro k
    have hh := Packet07DrivenCyclicPhaseAE.component_image_ae E
      (K ∩ body) (hK.inter hb.measurableSet) inside hiae k
    simpa only [hei'] using hh
  · intro k
    have hh := Packet07DrivenCyclicPhaseAE.component_image_ae E
      (K ∩ (closure body)ᶜ) (hK.inter isClosed_closure.measurableSet.compl)
      outside hoae k
    simpa only [heo'] using hh
  · intro phase y hy
    have hyA : h.symm y ∈ A := by
      rcases hy.1 with ⟨x,hx,rfl⟩
      simpa [h] using hx
    have hyphase : h.symm y ∈ phaseDomain body phase := by
      have hh := hy.2
      rw [← image_phase 1 (by norm_num) 0 body phase, (placement 1 (by norm_num) 0).image_eq_preimage] at hh
      exact hh
    rw [phase_transport,amplitude_transport]
    simpa [scale] using hbound phase _ ⟨hyA,hyphase⟩

end OQ14.Packet07DrivenCyclicTrace
#print axioms OQ14.Packet07DrivenCyclicTrace.cyclic_trace

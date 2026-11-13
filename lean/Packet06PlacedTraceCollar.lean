import Packet06PlacedActualPhase
import Packet06PlacementHomeomorph

/-! Transport actual one-sided branch identities and their whole-collar
pointwise bounds through the normalized physical placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06PlacedTraceCollar
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedKernel
open scoped Topology

theorem placed_trace_collar (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (body K A : Set Space) (hb : IsOpen body) (hK : MeasurableSet K) (hKball : K ⊆ ball (0 : Space) 1)
    (inside outside : Fin 3 → Space → ℂ)
    (hin : ∀ k, ContinuousOn (inside k) (K ∩ closure body))
    (hout : ∀ k, ContinuousOn (outside k) (K ∩ closure (closure body)ᶜ))
    (hiae : ∀ k, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x k) =ᵐ[volume.restrict (K ∩ body)] inside k)
    (hoae : ∀ k, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x k) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside k)
    (B : ℝ) (hbound : ∀ phase x, x ∈ A ∩ phaseDomain body phase →
      physicalAmplitude (phaseField inside outside phase) x ≤ B)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    let h := placement s hs a
    let E := Packet06ComplexElectric.electric ((s : ℂ)*z)
      (StaticCoefficient.sqrtMultiplier (placedCoefficient s a c) (placedUnknown s a u))
      (DynamicVolume.source (placedCoefficient s a c) (placedUnknown s a u))
    (∀ k, ContinuousOn (transport s hs a inside k) (h '' K ∩ closure (h '' body))) ∧
    (∀ k, ContinuousOn (transport s hs a outside k) (h '' K ∩ closure (closure (h '' body))ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body)] transport s hs a inside k) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body))ᶜ)] transport s hs a outside k) ∧
    ∀ phase y, y ∈ h '' A ∩ phaseDomain (h '' body) phase →
      physicalAmplitude (phaseField (transport s hs a inside) (transport s hs a outside) phase) y ≤ scale s*B := by
  dsimp only
  let h := placement s hs a
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
    exact continuous_transport s hs a inside _ hin k
  · intro k
    rw [← ho]
    exact continuous_transport s hs a outside _ hout k
  · intro k
    have hh := Packet06PlacedActualPhase.component_image_ae c hc hpos z u hu hN s hs a
      (K ∩ body) (hK.inter hb.measurableSet) (inter_subset_left.trans hKball) inside hiae k
    simpa only [hei'] using hh
  · intro k
    have hh := Packet06PlacedActualPhase.component_image_ae c hc hpos z u hu hN s hs a
      (K ∩ (closure body)ᶜ) (hK.inter isClosed_closure.measurableSet.compl)
      (inter_subset_left.trans hKball) outside hoae k
    simpa only [heo'] using hh
  · intro phase y hy
    have hyA : h.symm y ∈ A := by
      rcases hy.1 with ⟨x,hx,rfl⟩
      simpa [h] using hx
    have hyphase : h.symm y ∈ phaseDomain body phase := by
      have hh := hy.2
      rw [← image_phase s hs a body phase, (placement s hs a).image_eq_preimage] at hh
      exact hh
    rw [phase_transport,amplitude_transport]
    exact mul_le_mul_of_nonneg_left (hbound phase _ ⟨hyA,hyphase⟩) (scale_pos s hs).le

end OQ14.Packet06PlacedTraceCollar
#print axioms OQ14.Packet06PlacedTraceCollar.placed_trace_collar

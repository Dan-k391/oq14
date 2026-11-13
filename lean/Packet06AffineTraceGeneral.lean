import Packet06AffineActualPhaseGeneral
import Packet06PlacementHomeomorph

/-! Transport actual one-sided branch identities and their whole-collar
pointwise bounds through the normalized physical placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AffineTraceGeneral
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedKernel
open scoped Topology

theorem affine_trace_general (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (a : Space)
    (body K A : Set Space) (hb : IsOpen body) (hK : MeasurableSet K) (hKball : K ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ K, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (inside outside : Fin 3 → Space → ℂ)
    (hin : ∀ k, ContinuousOn (inside k) (K ∩ closure body))
    (hout : ∀ k, ContinuousOn (outside k) (K ∩ closure (closure body)ᶜ))
    (hiae : ∀ k, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x k) =ᵐ[volume.restrict (K ∩ body)] inside k)
    (hoae : ∀ k, (fun x => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) x k) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside k)
    (B : ℝ) (hbound : ∀ phase x, x ∈ A ∩ phaseDomain body phase →
      physicalAmplitude (phaseField inside outside phase) x ≤ B)
    :
    let h := placement 1 (by norm_num) a
    let E := Packet06ComplexElectric.electric z
      (StaticCoefficient.sqrtMultiplier (placedCoefficient 1 a c) (placedUnknown 1 a u))
      (DynamicVolume.source (placedCoefficient 1 a c) (placedUnknown 1 a u))
    (∀ k, ContinuousOn (transport 1 (by norm_num) a inside k) (h '' K ∩ closure (h '' body))) ∧
    (∀ k, ContinuousOn (transport 1 (by norm_num) a outside k) (h '' K ∩ closure (closure (h '' body))ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body)] transport 1 (by norm_num) a inside k) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body))ᶜ)] transport 1 (by norm_num) a outside k) ∧
    ∀ phase y, y ∈ h '' A ∩ phaseDomain (h '' body) phase →
      physicalAmplitude (phaseField (transport 1 (by norm_num) a inside) (transport 1 (by norm_num) a outside) phase) y ≤ B := by
  dsimp only
  let h := placement 1 (by norm_num) a
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
    exact continuous_transport 1 (by norm_num) a inside _ hin k
  · intro k
    rw [← ho]
    exact continuous_transport 1 (by norm_num) a outside _ hout k
  · intro k
    have hh := Packet06AffineActualPhaseGeneral.component_image_general_ae c R T hR hRT hc z u hu hN a
      (K ∩ body) (hK.inter hb.measurableSet) (inter_subset_left.trans hKball) (fun x hx => hpos x hx.1) inside hiae k
    simpa only [hei'] using hh
  · intro k
    have hh := Packet06AffineActualPhaseGeneral.component_image_general_ae c R T hR hRT hc z u hu hN a
      (K ∩ (closure body)ᶜ) (hK.inter isClosed_closure.measurableSet.compl)
      (inter_subset_left.trans hKball) (fun x hx => hpos x hx.1) outside hoae k
    simpa only [heo'] using hh
  · intro phase y hy
    have hyA : h.symm y ∈ A := by
      rcases hy.1 with ⟨x,hx,rfl⟩
      simpa [h] using hx
    have hyphase : h.symm y ∈ phaseDomain body phase := by
      have hh := hy.2
      rw [← image_phase 1 (by norm_num) a body phase, (placement 1 (by norm_num) a).image_eq_preimage] at hh
      exact hh
    rw [phase_transport,amplitude_transport]
    simpa [scale] using hbound phase _ ⟨hyA,hyphase⟩

end OQ14.Packet06AffineTraceGeneral
#print axioms OQ14.Packet06AffineTraceGeneral.affine_trace_general

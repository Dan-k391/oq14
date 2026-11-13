import Packet06AxialActualPhase
import Packet05OneSidedCollar

/-! Actual one-sided phase traces under arbitrary axial material rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialTraceCollar
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06AxialMaterialTransport Packet06AxialActualPhase Packet06AxialPhaseField

theorem rotated_trace_collar (θ : ℝ) (c : StaticCoefficient.Coefficient)
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
      physicalAmplitude (phaseField inside outside phase) x ≤ B) :
    let h := (rotation θ).toHomeomorph
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u))
    (∀ k, ContinuousOn (transport θ inside k) (h '' K ∩ closure (h '' body))) ∧
    (∀ k, ContinuousOn (transport θ outside k) (h '' K ∩ closure (closure (h '' body))ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body)] transport θ inside k) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body))ᶜ)] transport θ outside k) ∧
    ∀ phase y, y ∈ h '' A ∩ phaseDomain (h '' body) phase →
      physicalAmplitude (phaseField (transport θ inside) (transport θ outside) phase) y ≤ B := by
  dsimp only
  let h := (rotation θ).toHomeomorph
  have hi : h '' (K ∩ closure body) = h '' K ∩ closure (h '' body) := by
    rw [Set.image_inter h.injective,h.image_closure]
  have ho : h '' (K ∩ closure (closure body)ᶜ) = h '' K ∩ closure (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_closure,h.image_compl,h.image_closure]
  have hei : h '' (K ∩ body) = h '' K ∩ h '' body := by rw [Set.image_inter h.injective]
  have heo : h '' (K ∩ (closure body)ᶜ) = h '' K ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_compl,h.image_closure]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k
    rw [← hi]
    exact continuous_transport θ inside _ hin k
  · intro k
    rw [← ho]
    exact continuous_transport θ outside _ hout k
  · intro k
    have hh := component_image_ae θ c hc hpos z u hu hN (K ∩ body)
      (hK.inter hb.measurableSet) (inter_subset_left.trans hKball) inside hiae k
    change (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y k) =ᵐ[volume.restrict (h '' (K ∩ body))] transport θ inside k at hh
    rw [hei] at hh
    exact hh
  · intro k
    have hh := component_image_ae θ c hc hpos z u hu hN (K ∩ (closure body)ᶜ)
      (hK.inter isClosed_closure.measurableSet.compl) (inter_subset_left.trans hKball) outside hoae k
    change (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y k) =ᵐ[volume.restrict (h '' (K ∩ (closure body)ᶜ))] transport θ outside k at hh
    rw [heo] at hh
    exact hh
  · intro phase y hy
    obtain ⟨x,hx,rfl⟩ := hy.1
    have hphase : x ∈ phaseDomain body phase := by
      cases phase <;> simp only [phaseDomain] at hy ⊢
      · rw [← h.image_closure, ← h.image_compl, ← h.image_closure] at hy
        exact h.injective.mem_set_image.mp hy.2
      · rw [← h.image_closure] at hy
        exact h.injective.mem_set_image.mp hy.2
    rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hbound phase x ⟨hx,hphase⟩

theorem rotated_trace_collar_general (θ : ℝ) (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
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
      physicalAmplitude (phaseField inside outside phase) x ≤ B) :
    let h := (rotation θ).toHomeomorph
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u))
    (∀ k, ContinuousOn (transport θ inside k) (h '' K ∩ closure (h '' body))) ∧
    (∀ k, ContinuousOn (transport θ outside k) (h '' K ∩ closure (closure (h '' body))ᶜ)) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ h '' body)] transport θ inside k) ∧
    (∀ k, (fun y => E y k) =ᵐ[volume.restrict (h '' K ∩ (closure (h '' body))ᶜ)] transport θ outside k) ∧
    ∀ phase y, y ∈ h '' A ∩ phaseDomain (h '' body) phase →
      physicalAmplitude (phaseField (transport θ inside) (transport θ outside) phase) y ≤ B := by
  dsimp only
  let h := (rotation θ).toHomeomorph
  have hi : h '' (K ∩ closure body) = h '' K ∩ closure (h '' body) := by
    rw [Set.image_inter h.injective,h.image_closure]
  have ho : h '' (K ∩ closure (closure body)ᶜ) = h '' K ∩ closure (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_closure,h.image_compl,h.image_closure]
  have hei : h '' (K ∩ body) = h '' K ∩ h '' body := by rw [Set.image_inter h.injective]
  have heo : h '' (K ∩ (closure body)ᶜ) = h '' K ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,h.image_compl,h.image_closure]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k
    rw [← hi]
    exact continuous_transport θ inside _ hin k
  · intro k
    rw [← ho]
    exact continuous_transport θ outside _ hout k
  · intro k
    have hh := component_image_general_ae θ c R T hR hRT hc z u hu hN (K ∩ body)
      (hK.inter hb.measurableSet) (inter_subset_left.trans hKball) (fun x hx => hpos x hx.1) inside hiae k
    change (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y k) =ᵐ[volume.restrict (h '' (K ∩ body))] transport θ inside k at hh
    rw [hei] at hh
    exact hh
  · intro k
    have hh := component_image_general_ae θ c R T hR hRT hc z u hu hN (K ∩ (closure body)ᶜ)
      (hK.inter isClosed_closure.measurableSet.compl) (inter_subset_left.trans hKball) (fun x hx => hpos x hx.1) outside hoae k
    change (fun y => Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (coefficient θ c) (action θ u))
      (DynamicVolume.source (coefficient θ c) (action θ u)) y k) =ᵐ[volume.restrict (h '' (K ∩ (closure body)ᶜ))] transport θ outside k at hh
    rw [heo] at hh
    exact hh
  · intro phase y hy
    obtain ⟨x,hx,rfl⟩ := hy.1
    have hphase : x ∈ phaseDomain body phase := by
      cases phase <;> simp only [phaseDomain] at hy ⊢
      · rw [← h.image_closure, ← h.image_compl, ← h.image_closure] at hy
        exact h.injective.mem_set_image.mp hy.2
      · rw [← h.image_closure] at hy
        exact h.injective.mem_set_image.mp hy.2
    rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hbound phase x ⟨hx,hphase⟩

end OQ14.Packet06AxialTraceCollar
#print axioms OQ14.Packet06AxialTraceCollar.rotated_trace_collar
#print axioms OQ14.Packet06AxialTraceCollar.rotated_trace_collar_general

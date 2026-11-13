import Packet07DrivenUniformAffinePhase
import Packet07HotspotComponent

/-! Exact images of branch superlevels, maxima and their full connected
components under the physical Maxwell placement. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformAffineHotspotGeometry
open Set Metric Maxwell Packet07DrivenUniformAffineGeometry Packet07DrivenUniformAffinePhase
  Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet07HotspotComponent
abbrev Space := Maxwell.Space

theorem image_superlevel {J : Type*} (h : Space ≃ₜ Space) (D : J → Set Space)
    (amp : J → Space → ℝ) (t β : ℝ) (hβ : 0 < β) :
    h '' branchSuperlevel D amp t =
      branchSuperlevel (fun j => h '' D j) (fun j y => β*amp j (h.symm y)) (β*t) := by
  ext y
  rw [h.image_eq_preimage]
  simp only [mem_preimage, branchSuperlevel, mem_iUnion, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨j,hj,hlevel⟩
    exact ⟨j,⟨h.symm y,hj,h.apply_symm_apply y⟩,mul_le_mul_of_nonneg_left hlevel hβ.le⟩
  · rintro ⟨j,⟨x,hx,hxy⟩,hlevel⟩
    refine ⟨j,?_,(mul_le_mul_left hβ).mp hlevel⟩
    simpa only [← hxy,h.symm_apply_apply] using hx

theorem phase_superlevel_image (s : ℝ) (hs : 0 < s) (a : Space)
    (body : Set Space) (inside outside : Fin 3 → Space → ℂ) (t : ℝ) :
    placement s hs a '' branchSuperlevel (phaseDomain body)
      (fun b => physicalAmplitude (phaseField inside outside b)) t =
    branchSuperlevel (phaseDomain (placement s hs a '' body))
      (fun b => physicalAmplitude (phaseField (transport s hs a inside)
        (transport s hs a outside) b)) (s*t) := by
  rw [image_superlevel _ _ _ _ _ hs]
  simp only [image_phase, phase_transport, amplitude_transport]
  have he : (fun b => physicalAmplitude (transport s hs a (phaseField inside outside b))) =
      (fun b y => s*physicalAmplitude (phaseField inside outside b) ((placement s hs a).symm y)) := by
    funext b y
    exact amplitude_transport s hs a (phaseField inside outside b) y
  rw [he]

theorem maximum_transport (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ)
    (body : Set Space) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hx : x ∈ closedBall c r ∩ phaseDomain body b)
    (hmax : ∀ b' y, y ∈ closedBall c r ∩ phaseDomain body b' →
      physicalAmplitude (phaseField inside outside b') y ≤
        physicalAmplitude (phaseField inside outside b) x) :
    placement s hs a x ∈ closedBall (placement s hs a c) (r/s) ∩
      phaseDomain (placement s hs a '' body) b ∧
    ∀ b' y, y ∈ closedBall (placement s hs a c) (r/s) ∩
      phaseDomain (placement s hs a '' body) b' →
      physicalAmplitude (phaseField (transport s hs a inside) (transport s hs a outside) b') y ≤
        physicalAmplitude (phaseField (transport s hs a inside) (transport s hs a outside) b)
          (placement s hs a x) := by
  constructor
  · rw [← image_phase_ball]
    exact mem_image_of_mem _ hx
  · intro b' y hy
    rw [← image_phase_ball s hs a c r body b'] at hy
    obtain ⟨w,hw,rfl⟩ := hy
    simp only [phase_transport, amplitude_transport, (placement s hs a).symm_apply_apply]
    exact mul_le_mul_of_nonneg_left (hmax b' w hw) hs.le

theorem half_component_transport (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ)
    (body : Set Space) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hx : x ∈ branchSuperlevel (phaseDomain body)
      (fun b' => physicalAmplitude (phaseField inside outside b'))
      (physicalAmplitude (phaseField inside outside b) x/2))
    (hcompact : IsCompact (connectedComponentIn (branchSuperlevel (phaseDomain body)
      (fun b' => physicalAmplitude (phaseField inside outside b'))
      (physicalAmplitude (phaseField inside outside b) x/2)) x))
    (hinside : connectedComponentIn (branchSuperlevel (phaseDomain body)
      (fun b' => physicalAmplitude (phaseField inside outside b'))
      (physicalAmplitude (phaseField inside outside b) x/2)) x ⊆ ball c r) :
    let S := branchSuperlevel (phaseDomain (placement s hs a '' body))
      (fun b' => physicalAmplitude (phaseField (transport s hs a inside)
        (transport s hs a outside) b'))
      (physicalAmplitude (phaseField (transport s hs a inside) (transport s hs a outside) b)
        (placement s hs a x)/2)
    placement s hs a x ∈ connectedComponentIn S (placement s hs a x) ∧
      IsConnected (connectedComponentIn S (placement s hs a x)) ∧
      IsCompact (connectedComponentIn S (placement s hs a x)) ∧
      connectedComponentIn S (placement s hs a x) ⊆ ball (placement s hs a c) (r/s) := by
  let S₀ := branchSuperlevel (phaseDomain body)
    (fun b' => physicalAmplitude (phaseField inside outside b'))
    (physicalAmplitude (phaseField inside outside b) x/2)
  let h := placement s hs a
  have he : h '' S₀ = branchSuperlevel (phaseDomain (h '' body))
      (fun b' => physicalAmplitude (phaseField (transport s hs a inside)
        (transport s hs a outside) b'))
      (physicalAmplitude (phaseField (transport s hs a inside) (transport s hs a outside) b)
        (h x)/2) := by
    dsimp only [h,S₀]
    rw [phase_superlevel_image, phase_transport, amplitude_transport,
      (placement s hs a).symm_apply_apply, mul_div_assoc]
  dsimp only
  rw [← he, ← h.image_connectedComponentIn hx]
  have hmem : x ∈ connectedComponentIn S₀ x := mem_connectedComponentIn hx
  refine ⟨mem_image_of_mem h hmem,?_,hcompact.image h.continuous,?_⟩
  · exact (show IsConnected (connectedComponentIn S₀ x) from
      ⟨⟨x,hmem⟩,isPreconnected_connectedComponentIn⟩).image h h.continuous.continuousOn
  · rw [← image_ball s hs a c r]
    exact image_mono hinside

end OQ14.Packet07DrivenUniformAffineHotspotGeometry
#print axioms OQ14.Packet07DrivenUniformAffineHotspotGeometry.image_superlevel
#print axioms OQ14.Packet07DrivenUniformAffineHotspotGeometry.phase_superlevel_image
#print axioms OQ14.Packet07DrivenUniformAffineHotspotGeometry.maximum_transport
#print axioms OQ14.Packet07DrivenUniformAffineHotspotGeometry.half_component_transport

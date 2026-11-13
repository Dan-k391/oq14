import Packet07DrivenUniformAffineAE

/-! Exact affine transport of the actual attained driven hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenUniformAffineHotspot
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet07DrivenUniformAffineGeometry Packet07DrivenUniformAffinePhase Packet07DrivenUniformAffineHotspotGeometry
  Packet07DrivenUniformHotspot
abbrev Space := Maxwell.Space

theorem distance_placement (s : ℝ) (hs : 0 < s) (a x c : Space) :
    dist (placement s hs a x) (placement s hs a c)=s⁻¹*dist x c := by
  change ‖(s⁻¹ • x+a)-(s⁻¹ • c+a)‖ = s⁻¹*‖x-c‖
  have he : (s⁻¹ • x+a)-(s⁻¹ • c+a) = s⁻¹ • (x-c) := by module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]

theorem affine_actual_hotspot (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B)
    (s : ℝ) (hs : 0 < s) (a : Space) :
    HotspotAbove (Packet07AffineMaxwell.affineField s a E) (placement s hs a '' body)
      (placement s hs a center) (r/s) (s*M) (s*B) := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  let h := placement s hs a
  have hcl (k : Fin 3) : ContinuousOn (transport s hs a inside k)
      (closedBall (h center) (r/s) ∩ closure (h '' body)) := by
    have hh := continuous_transport s hs a inside (closedBall center r ∩ closure body) hi k
    have he := image_phase_ball s hs a center r body true
    change h '' (closedBall center r ∩ closure body) = _ at he
    rw [he] at hh
    exact hh
  have hco (k : Fin 3) : ContinuousOn (transport s hs a outside k)
      (closedBall (h center) (r/s) ∩ closure (closure (h '' body))ᶜ) := by
    have hh := continuous_transport s hs a outside (closedBall center r ∩ closure (closure body)ᶜ) ho k
    have he := image_phase_ball s hs a center r body false
    change h '' (closedBall center r ∩ closure (closure body)ᶜ) = _ at he
    rw [he] at hh
    exact hh
  have hei : h '' (closedBall center r ∩ body) = closedBall (h center) (r/s) ∩ h '' body := by
    rw [Set.image_inter h.injective,image_closedBall]
  have heo : h '' (closedBall center r ∩ (closure body)ᶜ) =
      closedBall (h center) (r/s) ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,image_closedBall,h.image_compl,h.image_closure]
  dsimp only [h] at hei heo
  have hia (k : Fin 3) := Packet07DrivenUniformAffineAE.component_image_ae s hs a E
    (closedBall center r ∩ body) (measurableSet_closedBall.inter hb.measurableSet) inside k (hiae k)
  have hoa (k : Fin 3) := Packet07DrivenUniformAffineAE.component_image_ae s hs a E
    (closedBall center r ∩ (closure body)ᶜ) (measurableSet_closedBall.inter isClosed_closure.measurableSet.compl) outside k (hoae k)
  have hpmax := maximum_transport s hs a center r body inside outside b x hx hmax
  have hamp (b' : Bool) (y : Space) : physicalAmplitude
      (phaseField (transport s hs a inside) (transport s hs a outside) b') y =
      s*physicalAmplitude (phaseField inside outside b') (h.symm y) := by
    rw [phase_transport,amplitude_transport]
  have hboundary (b' : Bool) (y : Space) (hy : y ∈ phaseDomain (h '' body) b')
      (hd : dist y (h center)=r/s) : physicalAmplitude
      (phaseField (transport s hs a inside) (transport s hs a outside) b') y ≤ s*B := by
    have hy' : h.symm y ∈ phaseDomain body b' := by
      rw [← image_phase s hs a body b',h.image_eq_preimage] at hy
      exact hy
    have hdist : dist (h.symm y) center=r := by
      have hh := distance_placement s hs a (h.symm y) center
      change dist (h (h.symm y)) (h center) = _ at hh
      rw [h.apply_symm_apply,hd,div_eq_mul_inv,mul_comm r s⁻¹] at hh
      exact (mul_left_cancel₀ (inv_ne_zero hs.ne') hh).symm
    rw [hamp]
    exact mul_le_mul_of_nonneg_left (hbd b' _ hy' hdist) hs.le
  have hcomponent := half_component_transport s hs a center r body inside outside b x
    (connectedComponentIn_subset _ _ hmem) hcomp hcontain
  refine ⟨transport s hs a inside,transport s hs a outside,hcl,hco,?_,?_,b,h x,
    hpmax.1,?_,?_,hpmax.2,hboundary,?_,hcomponent⟩
  · intro k
    simpa only [hei] using hia k
  · intro k
    simpa only [heo] using hoa k
  · rw [hamp,h.symm_apply_apply]
    exact mul_lt_mul_of_pos_left hM hs
  · rw [hamp,h.symm_apply_apply]
    nlinarith [mul_lt_mul_of_pos_left hB hs]
  · rw [← image_ball]
    exact mem_image_of_mem h hxr
end OQ14.Packet07DrivenUniformAffineHotspot
#print axioms OQ14.Packet07DrivenUniformAffineHotspot.distance_placement
#print axioms OQ14.Packet07DrivenUniformAffineHotspot.affine_actual_hotspot

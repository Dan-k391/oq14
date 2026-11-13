import Packet07DrivenAxialPhaseAE
import Packet06AxialHotspotGeometry
import Packet07DrivenUniformHotspot

/-! Proper axial rotation transports the actual driven hotspot and its full component. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialHotspot
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  ModalAxialRotation Packet06AxialPhaseField Packet07DrivenAxialPair Packet07DrivenUniformHotspot
abbrev Space := Maxwell.Space

theorem rotate_hotspot (θ : ℝ) (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (rotateField θ E) ((rotation θ) '' body) (rotation θ center) r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  let h := (rotation θ).toHomeomorph
  have himage : h '' closedBall center r = closedBall (rotation θ center) r :=
    Packet06AxialHotspotGeometry.image_closedBall θ center r
  have hci (k : Fin 3) : ContinuousOn (transport θ inside k)
      (closedBall (rotation θ center) r ∩ closure (h '' body)) := by
    have hh := continuous_transport θ inside _ hi k
    change ContinuousOn (transport θ inside k) (h '' (closedBall center r ∩ closure body)) at hh
    rw [Set.image_inter h.injective,himage,h.image_closure] at hh
    exact hh
  have hco (k : Fin 3) : ContinuousOn (transport θ outside k)
      (closedBall (rotation θ center) r ∩ closure (closure (h '' body))ᶜ) := by
    have hh := continuous_transport θ outside _ ho k
    change ContinuousOn (transport θ outside k) (h '' (closedBall center r ∩ closure (closure body)ᶜ)) at hh
    rw [Set.image_inter h.injective,himage,h.image_closure,h.image_compl,h.image_closure] at hh
    exact hh
  have hei : h '' (closedBall center r ∩ body) = closedBall (rotation θ center) r ∩ h '' body := by
    rw [Set.image_inter h.injective,himage]
  have heo : h '' (closedBall center r ∩ (closure body)ᶜ) =
      closedBall (rotation θ center) r ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective,himage,h.image_compl,h.image_closure]
  have heai (k : Fin 3) : (fun y => rotateField θ E y k) =ᵐ[
      volume.restrict (closedBall (rotation θ center) r ∩ h '' body)] transport θ inside k := by
    have hh := Packet07DrivenAxialPhaseAE.component_image_ae θ E (closedBall center r ∩ body)
      (measurableSet_closedBall.inter hb.measurableSet) inside hiae k
    change (fun y => rotateField θ E y k) =ᵐ[volume.restrict (h '' (closedBall center r ∩ body))] transport θ inside k at hh
    rwa [hei] at hh
  have heao (k : Fin 3) : (fun y => rotateField θ E y k) =ᵐ[
      volume.restrict (closedBall (rotation θ center) r ∩ (closure (h '' body))ᶜ)] transport θ outside k := by
    have hh := Packet07DrivenAxialPhaseAE.component_image_ae θ E (closedBall center r ∩ (closure body)ᶜ)
      (measurableSet_closedBall.inter isClosed_closure.measurableSet.compl) outside hoae k
    change (fun y => rotateField θ E y k) =ᵐ[volume.restrict (h '' (closedBall center r ∩ (closure body)ᶜ))] transport θ outside k at hh
    rwa [heo] at hh
  have hpmax := Packet06AxialHotspotGeometry.maximum_transport θ center r body inside outside b x hx hmax
  have hcomponent := Packet06AxialHotspotGeometry.half_component_transport θ center r body inside outside b x
    (connectedComponentIn_subset _ _ hmem) hcomp hcontain
  have hboundary (phase : Bool) (y : Space) (hy : y ∈ phaseDomain ((rotation θ) '' body) phase)
      (hd : dist y (rotation θ center)=r) :
      physicalAmplitude (phaseField (transport θ inside) (transport θ outside) phase) y ≤ B := by
    have hy' : rotation (-θ) y ∈ phaseDomain body phase := by
      rw [← Packet06AxialHotspotGeometry.image_phase θ body phase] at hy
      obtain ⟨w,hw,rfl⟩ := hy
      simpa [rotation,spatial_inverse] using hw
    have hd' : dist (rotation (-θ) y) center=r := by
      have hh := (rotation θ).dist_map (rotation (-θ) y) center
      have hinv : rotation θ (rotation (-θ) y)=y := by
        simpa only [neg_neg] using spatial_inverse (-θ) y
      rw [hinv,hd] at hh
      exact hh.symm
    rw [phase_transport,amplitude_transport]
    exact hbd phase _ hy' hd'
  refine ⟨transport θ inside,transport θ outside,hci,hco,heai,heao,b,rotation θ x,
    hpmax.1,?_,?_,hpmax.2,hboundary,?_,hcomponent⟩
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hM
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hB
  · rw [← Packet06AxialHotspotGeometry.image_ball θ center r]
    exact mem_image_of_mem _ hxr

end OQ14.Packet07DrivenAxialHotspot
#print axioms OQ14.Packet07DrivenAxialHotspot.rotate_hotspot

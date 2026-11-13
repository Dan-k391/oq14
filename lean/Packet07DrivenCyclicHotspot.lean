import Packet07DrivenCyclicTrace
import Packet07DrivenUniformHotspot
import Packet06AxialHotspot
import Packet06PlacedHotspotGeometry

/-! Cyclic rotation transports the actual hotspot and full component for
arbitrary support and local positive susceptibility. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenCyclicHotspot
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet07DrivenUniformHotspot Packet06PlacedKernel Packet06PlacementHomeomorph Packet06PlacedPhaseField
  Packet06PlacedHotspotGeometry
open scoped Topology
abbrev Space := Maxwell.Space

theorem cyclic_hotspot (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (Packet06CyclicRotationMaxwell.rotateField E)
      (placement 1 (by norm_num) 0 '' body) (placement 1 (by norm_num) 0 center) r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  let h := placement 1 (by norm_num) 0
  have htrace := Packet07DrivenCyclicTrace.cyclic_trace E body
    (closedBall center r) (closedBall center r) hb measurableSet_closedBall inside outside hi ho hiae hoae
    (physicalAmplitude (phaseField inside outside b) x) (fun phase y hy => hmax phase y hy)
  obtain ⟨hci,hco,heai,heao,_⟩ := htrace
  have himage : h '' closedBall center r = closedBall (h center) r := by
    simpa [h] using image_closedBall 1 (by norm_num) 0 center r
  rw [himage] at hci hco heai heao
  have hpmax := maximum_transport 1 (by norm_num) 0 center r body inside outside b x hx hmax
  have hcomponent := half_component_transport 1 (by norm_num) 0 center r body inside outside b x
    (connectedComponentIn_subset _ _ hmem) hcomp hcontain
  have hboundary (phase : Bool) (y : Space) (hy : y ∈ phaseDomain (h '' body) phase)
      (hd : dist y (h center)=r) : physicalAmplitude
      (phaseField (transport 1 (by norm_num) 0 inside) (transport 1 (by norm_num) 0 outside) phase) y ≤ B := by
    have hy' : h.symm y ∈ phaseDomain body phase := by
      rw [← image_phase 1 (by norm_num) 0 body phase, h.image_eq_preimage] at hy
      exact hy
    have hdist : dist (h.symm y) center=r := by
      have hh := Packet06PlanarProjection.point_distance_pair 1 (by norm_num) 0 (h.symm y) center
      change dist (h (h.symm y)) (h center) = _ at hh
      rw [h.apply_symm_apply,hd] at hh
      simpa using hh.symm
    rw [phase_transport,amplitude_transport]
    simpa [scale] using hbd phase _ hy' hdist
  refine ⟨transport 1 (by norm_num) 0 inside,transport 1 (by norm_num) 0 outside,hci,hco,heai,heao,b,h x,
    ?_,?_,?_,?_,hboundary,?_,?_⟩
  · simpa [h] using hpmax.1
  · rw [phase_transport,amplitude_transport,h.symm_apply_apply]
    simpa [scale] using hM
  · rw [phase_transport,amplitude_transport,h.symm_apply_apply]
    simpa [scale] using hB
  · simpa [h] using hpmax.2
  · have hh := image_ball 1 (by norm_num) 0 center r
    simp only [div_one] at hh
    rw [← hh]
    exact mem_image_of_mem h hxr
  · simpa [h] using hcomponent
end OQ14.Packet07DrivenCyclicHotspot
#print axioms OQ14.Packet07DrivenCyclicHotspot.cyclic_hotspot

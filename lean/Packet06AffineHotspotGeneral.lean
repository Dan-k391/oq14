import Packet06AffineTraceGeneral
import Packet06AxialHotspot
import Packet06PlacedHotspotGeometry

/-! Cyclic rotation followed by arbitrary translation transports the actual hotspot and full component for
arbitrary support and local positive susceptibility. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AffineHotspotGeneral
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06AxialHotspot Packet06PlacedKernel Packet06PlacementHomeomorph Packet06PlacedPhaseField
  Packet06PlacedHotspotGeometry
open scoped Topology
abbrev Space := Maxwell.Space

theorem affine_hotspot_general (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1) (a : Space)
    (body P : Set Space) (hb : IsOpen body) (center : Space) (r M B : ℝ)
    (hball : closedBall center r ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ closedBall center r, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hhot : AxialHotspot c z u body P center r M B) :
    AxialHotspot (placedCoefficient 1 a c) z (placedUnknown 1 a u)
      (placement 1 (by norm_num) a '' body) (placement 1 (by norm_num) a '' P)
      (placement 1 (by norm_num) a center) r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  let h := placement 1 (by norm_num) a
  have htrace := Packet06AffineTraceGeneral.affine_trace_general c R T hR hRT hc z u hu hN a body
    (closedBall center r) (closedBall center r) hb measurableSet_closedBall hball hpos inside outside hi ho hiae hoae
    (physicalAmplitude (phaseField inside outside b) x) (fun phase y hy => hmax phase y hy)
  obtain ⟨hci,hco,heai,heao,_⟩ := htrace
  have himage : h '' closedBall center r = closedBall (h center) r := by
    simpa [h] using image_closedBall 1 (by norm_num) a center r
  rw [himage] at hci hco heai heao
  have hpmax := maximum_transport 1 (by norm_num) a center r body inside outside b x hx hmax
  have hcomponent := half_component_transport 1 (by norm_num) a center r body inside outside b x
    (connectedComponentIn_subset _ _ hmem) hcomp hcontain
  have hboundary (phase : Bool) (y : Space) (hy : y ∈ phaseDomain (h '' body) phase)
      (hd : dist y (h center)=r) : physicalAmplitude
      (phaseField (transport 1 (by norm_num) a inside) (transport 1 (by norm_num) a outside) phase) y ≤ B := by
    have hy' : h.symm y ∈ phaseDomain body phase := by
      rw [← image_phase 1 (by norm_num) a body phase, h.image_eq_preimage] at hy
      exact hy
    have hdist : dist (h.symm y) center=r := by
      have hh := Packet06PlanarProjection.point_distance_pair 1 (by norm_num) a (h.symm y) center
      change dist (h (h.symm y)) (h center) = _ at hh
      rw [h.apply_symm_apply,hd] at hh
      simpa using hh.symm
    rw [phase_transport,amplitude_transport]
    simpa [scale] using hbd phase _ hy' hdist
  refine ⟨transport 1 (by norm_num) a inside,transport 1 (by norm_num) a outside,hci,hco,heai,heao,b,h x,
    ?_,mem_image_of_mem h hplane,?_,?_,?_,hboundary,?_,?_⟩
  · simpa [h] using hpmax.1
  · rw [phase_transport,amplitude_transport,h.symm_apply_apply]
    simpa [scale] using hM
  · rw [phase_transport,amplitude_transport,h.symm_apply_apply]
    simpa [scale] using hB
  · simpa [h] using hpmax.2
  · have hh := image_ball 1 (by norm_num) a center r
    simp only [div_one] at hh
    rw [← hh]
    exact mem_image_of_mem h hxr
  · simpa [h] using hcomponent
end OQ14.Packet06AffineHotspotGeneral
#print axioms OQ14.Packet06AffineHotspotGeneral.affine_hotspot_general

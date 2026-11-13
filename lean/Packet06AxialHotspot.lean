import Packet06AxialHotspotGeometry
import Packet06PlacedHotspot

/-! The full actual phase hotspot predicate on a specified spatial plane. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AxialHotspot
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  ModalAxialRotation Packet06AxialMaterialTransport Packet06AxialPhaseField
def AxialHotspot (c : StaticCoefficient.Coefficient) (z : ℂ)
    (v : VectorFourier.VectorL2) (body P : Set Space) (center : Space) (r M B : ℝ) : Prop :=
  let K := closedBall center r
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c v)
    (DynamicVolume.source c v)
  ∃ inside outside : Fin 3 → Space → ℂ,
    (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
    (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) ∧
    ∃ b x, x ∈ K ∩ phaseDomain body b ∧ x ∈ P ∧
      M < physicalAmplitude (phaseField inside outside b) x ∧
      2*B < physicalAmplitude (phaseField inside outside b) x ∧
      (∀ b' y, y ∈ K ∩ phaseDomain body b' →
        physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x) ∧
      (∀ b' y, y ∈ phaseDomain body b' → dist y center=r → physicalAmplitude (phaseField inside outside b') y ≤ B) ∧
      let S := Packet07HotspotComponent.branchSuperlevel (phaseDomain body)
        (fun b' => physicalAmplitude (phaseField inside outside b')) (physicalAmplitude (phaseField inside outside b) x/2)
      x ∈ ball center r ∧ x ∈ connectedComponentIn S x ∧
        IsConnected (connectedComponentIn S x) ∧ IsCompact (connectedComponentIn S x) ∧
        connectedComponentIn S x ⊆ ball center r

theorem rotate_hotspot (θ : ℝ) (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (body P : Set Space) (hb : IsOpen body) (center : Space) (r M B : ℝ)
    (hball : closedBall center r ⊆ ball (0 : Space) 1)
    (hhot : AxialHotspot c z u body P center r M B) :
    AxialHotspot (coefficient θ c) z (action θ u) ((rotation θ) '' body) ((rotation θ) '' P)
      (rotation θ center) r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  have htrace := Packet06AxialTraceCollar.rotated_trace_collar θ c hc hpos z u hu hN body
    (closedBall center r) (closedBall center r) hb measurableSet_closedBall hball inside outside hi ho hiae hoae
    (physicalAmplitude (phaseField inside outside b) x) (fun phase y hy => hmax phase y hy)
  obtain ⟨hci,hco,heai,heao,_⟩ := htrace
  let h := (rotation θ).toHomeomorph
  have hballimage : h '' closedBall center r = closedBall (rotation θ center) r :=
    Packet06AxialHotspotGeometry.image_closedBall θ center r
  rw [hballimage] at hci hco heai heao
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
    hpmax.1,mem_image_of_mem _ hplane,?_,?_,hpmax.2,hboundary,?_,hcomponent⟩
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hM
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hB
  · rw [← Packet06AxialHotspotGeometry.image_ball θ center r]
    exact mem_image_of_mem _ hxr

theorem rotate_hotspot_general (θ : ℝ) (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (body P : Set Space) (hb : IsOpen body) (center : Space) (r M B : ℝ)
    (hball : closedBall center r ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ closedBall center r, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hhot : AxialHotspot c z u body P center r M B) :
    AxialHotspot (coefficient θ c) z (action θ u) ((rotation θ) '' body) ((rotation θ) '' P)
      (rotation θ center) r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
  have htrace := Packet06AxialTraceCollar.rotated_trace_collar_general θ c R T hR hRT hc z u hu hN body
    (closedBall center r) (closedBall center r) hb measurableSet_closedBall hball hpos inside outside hi ho hiae hoae
    (physicalAmplitude (phaseField inside outside b) x) (fun phase y hy => hmax phase y hy)
  obtain ⟨hci,hco,heai,heao,_⟩ := htrace
  let h := (rotation θ).toHomeomorph
  have hballimage : h '' closedBall center r = closedBall (rotation θ center) r :=
    Packet06AxialHotspotGeometry.image_closedBall θ center r
  rw [hballimage] at hci hco heai heao
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
    hpmax.1,mem_image_of_mem _ hplane,?_,?_,hpmax.2,hboundary,?_,hcomponent⟩
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hM
  · rw [phase_transport,amplitude_transport]
    simpa [rotation,spatial_inverse] using hB
  · rw [← Packet06AxialHotspotGeometry.image_ball θ center r]
    exact mem_image_of_mem _ hxr

end OQ14.Packet06AxialHotspot
#print axioms OQ14.Packet06AxialHotspot.rotate_hotspot
#print axioms OQ14.Packet06AxialHotspot.rotate_hotspot_general

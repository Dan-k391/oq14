import Packet06RoundedHotspot
import Packet06PlacedHotspotGeometry
import Packet06PlacedActualPhase

/-! The same attained one-sided hotspot, now for the actual normalized
placed Maxwell field and on the prescribed physical plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedHotspot
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedKernel
  Packet06PlacedHotspotGeometry
open scoped Topology

def PhysicalHotspot (c : StaticCoefficient.Coefficient) (z : ℂ)
    (v : VectorFourier.VectorL2) (body : Set Space) (center : Space) (r M B : ℝ) : Prop :=
  let K := closedBall center r
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c v)
    (DynamicVolume.source c v)
  ∃ inside outside : Fin 3 → Space → ℂ,
    (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
    (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) ∧
    ∃ b x, x ∈ K ∩ phaseDomain body b ∧ x 2=0 ∧
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

theorem placed_actual_hotspot (c : StaticCoefficient.Coefficient)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (body : Set Space) (hb : IsOpen body) (center : Space) (r M B : ℝ)
    (hball : closedBall center r ⊆ ball (0 : Space) 1)
    (hhot : Packet06RoundedHotspot.HotspotAbove c z u body center r M B)
    (s : ℝ) (hs : 0 < s) (a : Space) (ha : a 2=0) :
    PhysicalHotspot (placedCoefficient s a c) ((s : ℂ)*z) (placedUnknown s a u)
      (placement s hs a '' body) (placement s hs a center) (r/s) (scale s*M) (scale s*B) := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hM,hB,hmax,hbd,hxr,hmem,hconn,hcomp,hcontain⟩ := hhot
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
    rw [Set.image_inter h.injective, image_closedBall]
  have heo : h '' (closedBall center r ∩ (closure body)ᶜ) =
      closedBall (h center) (r/s) ∩ (closure (h '' body))ᶜ := by
    rw [Set.image_inter h.injective, image_closedBall, h.image_compl, h.image_closure]
  dsimp only [h] at hei heo
  have hia (k : Fin 3) := Packet06PlacedActualPhase.component_image_ae c hc hpos z u hu hN s hs a
    (closedBall center r ∩ body) (measurableSet_closedBall.inter hb.measurableSet)
    (inter_subset_left.trans hball) inside hiae k
  have hoa (k : Fin 3) := Packet06PlacedActualPhase.component_image_ae c hc hpos z u hu hN s hs a
    (closedBall center r ∩ (closure body)ᶜ) (measurableSet_closedBall.inter isClosed_closure.measurableSet.compl)
    (inter_subset_left.trans hball) outside hoae k
  have hpmax := maximum_transport s hs a center r body inside outside b x hx hmax
  have hamp (b' : Bool) (y : Space) : physicalAmplitude
      (phaseField (transport s hs a inside) (transport s hs a outside) b') y =
      scale s*physicalAmplitude (phaseField inside outside b') (h.symm y) := by
    rw [phase_transport, amplitude_transport]
  have hboundary (b' : Bool) (y : Space) (hy : y ∈ phaseDomain (h '' body) b')
      (hd : dist y (h center)=r/s) : physicalAmplitude
      (phaseField (transport s hs a inside) (transport s hs a outside) b') y ≤ scale s*B := by
    have hy' : h.symm y ∈ phaseDomain body b' := by
      rw [← image_phase s hs a body b', h.image_eq_preimage] at hy
      exact hy
    have hdist : dist (h.symm y) center=r := by
      have hh := Packet06PlanarProjection.point_distance_pair s hs a (h.symm y) center
      change dist (h (h.symm y)) (h center) = _ at hh
      rw [h.apply_symm_apply,hd,div_eq_mul_inv,mul_comm r s⁻¹] at hh
      exact (mul_left_cancel₀ (inv_ne_zero hs.ne') hh).symm
    rw [hamp]
    exact mul_le_mul_of_nonneg_left (hbd b' _ hy' hdist) (scale_pos s hs).le
  have hcomponent := half_component_transport s hs a center r body inside outside b x
    (connectedComponentIn_subset _ _ hmem) hcomp hcontain
  refine ⟨transport s hs a inside,transport s hs a outside,hcl,hco,?_,?_,b,h x,
    hpmax.1,Packet07MeridionalMaximum.placed_meridian_is_planar s a x ha hplane,?_,?_,
    hpmax.2,hboundary,?_,hcomponent⟩
  · intro k
    simpa only [hei] using hia k
  · intro k
    simpa only [heo] using hoa k
  · rw [hamp,h.symm_apply_apply]
    exact mul_lt_mul_of_pos_left hM (scale_pos s hs)
  · rw [hamp,h.symm_apply_apply]
    nlinarith [mul_lt_mul_of_pos_left hB (scale_pos s hs)]
  · rw [← image_ball]
    exact mem_image_of_mem h hxr

end OQ14.Packet06PlacedHotspot
#print axioms OQ14.Packet06PlacedHotspot.placed_actual_hotspot

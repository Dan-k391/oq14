import Packet06CyclicHotspotGeneral
import Packet06CyclicOneSidedGeneral

/-! Two forward cyclic transports give the inverse cyclic leg while retaining
the same actual Maxwell hotspot and local material positivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06CyclicTwiceGeneral
open MeasureTheory Set Metric Maxwell Packet05OneSidedCollar Packet06AxialHotspot
  Packet06PlacedKernel Packet06PlacementHomeomorph Packet06CyclicRotation
abbrev Space := Maxwell.Space

def h : Space ≃ₜ Space := placement 1 (by norm_num) 0

theorem coefficient_image (c : StaticCoefficient.Coefficient) (x : Space) :
    (placedCoefficient 1 0 c).value (VectorFourier.coordinateMap (h x)) =
      c.value (VectorFourier.coordinateMap x) := by
  simp [placedCoefficient,Packet06TranslationMaterial.coefficient_value,FrequencyScalingMaxwell.scaleCoeff,
    Packet06CyclicMaterial.coefficient_value,h,placement,Packet06PhysicalPlacement.point,unrotate_rotate]

theorem ball_image (c : Space) (r : ℝ) : h '' closedBall c r = closedBall (h c) r := by
  simpa [h] using image_closedBall 1 (by norm_num) 0 c r

theorem twice_hotspot (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (body P : Set Space) (hb : IsOpen body) (center : Space) (r M B : ℝ)
    (hball : closedBall center r ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ closedBall center r, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hhot : AxialHotspot c z u body P center r M B) :
    AxialHotspot (placedCoefficient 1 0 (placedCoefficient 1 0 c)) z
      (placedUnknown 1 0 (placedUnknown 1 0 u)) (h '' (h '' body)) (h '' (h '' P)) (h (h center)) r M B := by
  have hfirst := Packet06CyclicHotspotGeneral.cyclic_hotspot_general c R T hR hRT hc z u hu hN
    body P hb center r M B hball hpos hhot
  obtain ⟨hc',hu',hN',_⟩ := placed_normalized_kernel c R hR hc z u hu hN 1 (by norm_num) 0
  simp only [div_one,norm_zero,add_zero,Complex.ofReal_one,one_mul] at hc' hu' hN'
  have hball' : closedBall (h center) r ⊆ closedBall (0 : Space) T := by
    rw [← ball_image]
    rintro y ⟨x,hx,rfl⟩
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right,rotate_norm] using hball hx
  have hpos' : ∀ y ∈ closedBall (h center) r,
      (placedCoefficient 1 0 c).value (VectorFourier.coordinateMap y) ≠ 0 := by
    rw [← ball_image]
    rintro y ⟨x,hx,rfl⟩
    rw [coefficient_image]
    exact hpos x hx
  exact Packet06CyclicHotspotGeneral.cyclic_hotspot_general (placedCoefficient 1 0 c) R T hR hRT hc' z
    (placedUnknown 1 0 u) hu' hN' (h '' body) (h '' P) (h.isOpenMap _ hb) (h center) r M B hball' hpos' hfirst
end OQ14.Packet06CyclicTwiceGeneral
#print axioms OQ14.Packet06CyclicTwiceGeneral.coefficient_image
#print axioms OQ14.Packet06CyclicTwiceGeneral.ball_image
#print axioms OQ14.Packet06CyclicTwiceGeneral.twice_hotspot

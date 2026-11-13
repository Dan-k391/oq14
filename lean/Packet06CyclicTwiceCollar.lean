import Packet06CyclicTwiceGeneral

/-! Two cyclic transports of a genuine local one-sided collar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06CyclicTwiceCollar
open MeasureTheory Set Metric Maxwell Packet05OneSidedCollar Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06CyclicRotation Packet06CyclicTwiceGeneral
abbrev Space := Maxwell.Space

theorem twice_collar (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (body A : Set Space) (hb : IsOpen body) (hA : IsOpen A) (hball : A ⊆ closedBall (0 : Space) T)
    (hpos : ∀ x ∈ A, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (B : ℝ) (hcollar : OneSidedCollar c z u body A B) :
    OneSidedCollar (placedCoefficient 1 0 (placedCoefficient 1 0 c)) z
      (placedUnknown 1 0 (placedUnknown 1 0 u)) (h '' (h '' body)) (h '' (h '' A)) B := by
  have hfirst := Packet06CyclicOneSidedGeneral.cyclic_one_sided_general c R T hR hRT hc z u hu hN body A
    hb hA hball hpos B hcollar
  obtain ⟨hc',hu',hN',_⟩ := placed_normalized_kernel c R hR hc z u hu hN 1 (by norm_num) 0
  simp only [div_one,norm_zero,add_zero,Complex.ofReal_one,one_mul] at hc' hu' hN'
  have hball' : h '' A ⊆ closedBall (0 : Space) T := by
    rintro y ⟨x,hx,rfl⟩
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right,rotate_norm] using hball hx
  have hpos' : ∀ y ∈ h '' A, (placedCoefficient 1 0 c).value (VectorFourier.coordinateMap y) ≠ 0 := by
    rintro y ⟨x,hx,rfl⟩
    rw [coefficient_image]
    exact hpos x hx
  exact Packet06CyclicOneSidedGeneral.cyclic_one_sided_general (placedCoefficient 1 0 c) R T hR hRT hc' z
    (placedUnknown 1 0 u) hu' hN' (h '' body) (h '' A) (h.isOpenMap _ hb) (h.isOpenMap _ hA)
    hball' hpos' B hfirst
end OQ14.Packet06CyclicTwiceCollar
#print axioms OQ14.Packet06CyclicTwiceCollar.twice_collar

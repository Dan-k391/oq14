import Packet06AxialHotspotStart
import Packet06CyclicHotspotGeneral
import Packet06CyclicTwiceGeneral
import Packet06AffineHotspotGeneral

/-! A composable physical hotspot witness under actual rigid motions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06RigidHotspotState
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet06AxialHotspot
  Packet06AxialMaterialTransport Packet06AxialOutgoingTransport Packet06AxialHotspotGeometry
  Packet06PlacedKernel Packet06PlacementHomeomorph
abbrev Space := Maxwell.Space

structure State (N : ℕ) (z : ℂ) (r M B : ℝ) where
  material : StaticCoefficient.Coefficient
  unknown : VectorFourier.VectorL2
  supportRadius : ℝ
  support_nonnegative : 0 ≤ supportRadius
  support : ∀ x : Space, x ∉ closedBall 0 supportRadius → material.value (VectorFourier.coordinateMap x)=0
  kernel : ComplexConvolutionAnalytic.volumeBlock material z supportRadius unknown=0
  normalization : Packet06PhysicalNormalization.reciprocalNorm material supportRadius z unknown=1
  body : Set Space
  plane : Set Space
  center : Fin N → Space
  body_open : IsOpen body
  ball_support : ∀ i, closedBall (center i) r ⊆ closedBall 0 supportRadius
  ball_positive : ∀ i x, x ∈ closedBall (center i) r → material.value (VectorFourier.coordinateMap x) ≠ 0
  hotspots : ∀ i, AxialHotspot material z unknown body plane (center i) r M B

def axial {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B) : State N z r M B := by
  have hfacts := rotated_normalized_mode θ d.material z d.supportRadius d.support_nonnegative d.support d.unknown d.kernel d.normalization
  let h := (rotation θ).toHomeomorph
  refine ⟨coefficient θ d.material,action θ d.unknown,d.supportRadius,d.support_nonnegative,hfacts.1,hfacts.2.1,hfacts.2.2.1,
    h '' d.body,h '' d.plane,fun i => h (d.center i),h.isOpenMap _ d.body_open,?_,?_,?_⟩
  · intro i
    change closedBall (rotation θ (d.center i)) r ⊆ closedBall 0 d.supportRadius
    rw [← image_closedBall θ (d.center i) r]
    rintro y ⟨x,hx,rfl⟩
    simpa [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using d.ball_support i hx
  · intro i y hy
    change y ∈ closedBall (rotation θ (d.center i)) r at hy
    rw [← image_closedBall θ (d.center i) r] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [coefficient_value]
    simpa [rotation,spatial_inverse] using d.ball_positive i x hx
  · intro i
    exact rotate_hotspot_general θ d.material d.supportRadius d.supportRadius d.support_nonnegative le_rfl d.support
      z d.unknown d.kernel d.normalization d.body d.plane d.body_open (d.center i) r M B
      (d.ball_support i) (d.ball_positive i) (d.hotspots i)

def cyclic {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) : State N z r M B := by
  let h := placement 1 (by norm_num) 0
  have hfacts := placed_normalized_kernel d.material d.supportRadius d.support_nonnegative d.support
    z d.unknown d.kernel d.normalization 1 (by norm_num) 0
  have hs : ∀ x : Space, x ∉ closedBall 0 d.supportRadius → (placedCoefficient 1 0 d.material).value (VectorFourier.coordinateMap x)=0 := by
    simpa only [div_one,norm_zero,add_zero] using hfacts.1
  have hk : ComplexConvolutionAnalytic.volumeBlock (placedCoefficient 1 0 d.material) z d.supportRadius (placedUnknown 1 0 d.unknown)=0 := by
    simpa only [div_one,norm_zero,add_zero,Complex.ofReal_one,one_mul] using hfacts.2.1
  have hn : Packet06PhysicalNormalization.reciprocalNorm (placedCoefficient 1 0 d.material) d.supportRadius z (placedUnknown 1 0 d.unknown)=1 := by
    simpa only [div_one,norm_zero,add_zero,Complex.ofReal_one,one_mul] using hfacts.2.2.1
  refine ⟨placedCoefficient 1 0 d.material,placedUnknown 1 0 d.unknown,d.supportRadius,
    d.support_nonnegative,hs,hk,hn,h '' d.body,h '' d.plane,fun i => h (d.center i),
    h.isOpenMap _ d.body_open,?_,?_,?_⟩
  · intro i
    have he : h '' closedBall (d.center i) r = closedBall (h (d.center i)) r := by
      simpa [h] using image_closedBall 1 (by norm_num) 0 (d.center i) r
    rw [← he]
    rintro y ⟨x,hx,rfl⟩
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right,
      Packet06CyclicRotation.rotate_norm] using d.ball_support i hx
  · intro i y hy
    have he : h '' closedBall (d.center i) r = closedBall (h (d.center i)) r := by
      simpa [h] using image_closedBall 1 (by norm_num) 0 (d.center i) r
    change y ∈ closedBall (h (d.center i)) r at hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    change (placedCoefficient 1 0 d.material).value
      (VectorFourier.coordinateMap (Packet06CyclicTwiceGeneral.h x)) ≠ 0
    rw [Packet06CyclicTwiceGeneral.coefficient_image]
    exact d.ball_positive i x hx
  · intro i
    exact Packet06CyclicHotspotGeneral.cyclic_hotspot_general d.material d.supportRadius d.supportRadius
      d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization d.body d.plane d.body_open
      (d.center i) r M B (d.ball_support i) (d.ball_positive i) (d.hotspots i)

#print axioms OQ14.Packet06RigidHotspotState.axial
#print axioms OQ14.Packet06RigidHotspotState.cyclic

end OQ14.Packet06RigidHotspotState

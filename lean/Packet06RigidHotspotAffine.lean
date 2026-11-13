import Packet06RigidHotspotState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.Packet06RigidHotspotState
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet06AxialHotspot
  Packet06AxialMaterialTransport Packet06AxialOutgoingTransport Packet06AxialHotspotGeometry
  Packet06PlacedKernel Packet06PlacementHomeomorph
def affine {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B) : State N z r M B := by
  let h := placement 1 (by norm_num) a
  have hfacts := placed_normalized_kernel d.material d.supportRadius d.support_nonnegative d.support
    z d.unknown d.kernel d.normalization 1 (by norm_num) a
  have hs : ∀ x : Space, x ∉ closedBall 0 (d.supportRadius+‖a‖) → (placedCoefficient 1 a d.material).value (VectorFourier.coordinateMap x)=0 := by
    simpa only [div_one] using hfacts.1
  have hk : ComplexConvolutionAnalytic.volumeBlock (placedCoefficient 1 a d.material) z (d.supportRadius+‖a‖) (placedUnknown 1 a d.unknown)=0 := by
    simpa only [div_one,Complex.ofReal_one,one_mul] using hfacts.2.1
  have hn : Packet06PhysicalNormalization.reciprocalNorm (placedCoefficient 1 a d.material) (d.supportRadius+‖a‖) z (placedUnknown 1 a d.unknown)=1 := by
    simpa only [div_one,Complex.ofReal_one,one_mul] using hfacts.2.2.1
  refine ⟨placedCoefficient 1 a d.material,placedUnknown 1 a d.unknown,d.supportRadius+‖a‖,
    add_nonneg d.support_nonnegative (norm_nonneg a),hs,hk,hn,h '' d.body,h '' d.plane,
    fun i => h (d.center i),h.isOpenMap _ d.body_open,?_,?_,?_⟩
  · intro i
    have he : h '' closedBall (d.center i) r = closedBall (h (d.center i)) r := by
      simpa [h] using image_closedBall 1 (by norm_num) a (d.center i) r
    change closedBall (h (d.center i)) r ⊆ closedBall 0 (d.supportRadius+‖a‖)
    rw [← he]
    rintro y ⟨x,hx,rfl⟩
    have hx' : ‖x‖ ≤ d.supportRadius := by simpa [mem_closedBall,dist_zero_right] using d.ball_support i hx
    have hh := norm_add_le a (Packet06CyclicRotation.rotate x)
    have hrot : ‖Packet06CyclicRotation.rotate x‖ = ‖x‖ := Packet06CyclicRotation.rotate_norm x
    have hpoint : h x = a + Packet06CyclicRotation.rotate x := by
      change Packet06PhysicalPlacement.point 1 a x = _
      simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
    rw [mem_closedBall,dist_zero_right,hpoint]
    rw [hrot] at hh
    linarith
  · intro i y hy
    have he : h '' closedBall (d.center i) r = closedBall (h (d.center i)) r := by
      simpa [h] using image_closedBall 1 (by norm_num) a (d.center i) r
    change y ∈ closedBall (h (d.center i)) r at hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb : Packet06CyclicRotation.unrotate ((1 : ℝ) • (h x-a))=x := by
      have hp : h x = a + Packet06CyclicRotation.rotate x := by
        change Packet06PhysicalPlacement.point 1 a x = _
        simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
      rw [hp]
      simp only [add_sub_cancel_left,one_smul,Packet06CyclicRotation.unrotate_rotate]
    exact fun hz => d.ball_positive i x hx ((congrArg (fun y => d.material.value (VectorFourier.coordinateMap y)) hb).symm.trans hz)
  · intro i
    exact Packet06AffineHotspotGeneral.affine_hotspot_general d.material d.supportRadius d.supportRadius
      d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization a d.body d.plane d.body_open
      (d.center i) r M B (d.ball_support i) (d.ball_positive i) (d.hotspots i)


#print axioms OQ14.Packet06RigidHotspotState.affine
end OQ14.Packet06RigidHotspotState

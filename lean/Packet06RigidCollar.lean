import Packet06RigidHotspotAffine
import Packet06CyclicOneSidedGeneral
import Packet06AffineOneSidedGeneral

/-! Fixed actual one-sided collars can be transported along a hotspot state. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidCollar
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet06RigidHotspotState Packet05OneSidedCollar
  Packet06AxialMaterialTransport Packet06AxialPhaseField Packet06PlacedKernel Packet06PlacementHomeomorph
abbrev Space := Maxwell.Space

def HasCollars {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) (A : Fin N → Set Space) : Prop :=
  ∀ i, IsOpen (A i) ∧ A i ⊆ closedBall 0 d.supportRadius ∧
    (∀ x ∈ A i, d.material.value (VectorFourier.coordinateMap x) ≠ 0) ∧
    sphere (d.center i) r ⊆ A i ∧ OneSidedCollar d.material z d.unknown d.body (A i) B

theorem axial_collar {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B)
    (A : Fin N → Set Space) (hA : HasCollars d A) :
    HasCollars (axial θ d) (fun i => (rotation θ) '' A i) := by
  intro i
  obtain ⟨ho,hs,hpos,hsphere,hcollar⟩ := hA i
  let h := (rotation θ).toHomeomorph
  refine ⟨h.isOpenMap _ ho,?_,?_,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    simpa [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using hs hx
  · rintro y ⟨x,hx,rfl⟩
    change (Packet06AxialMaterialTransport.coefficient θ d.material).value (VectorFourier.coordinateMap (rotation θ x)) ≠ 0
    rw [Packet06AxialMaterialTransport.coefficient_value]
    simpa [rotation,spatial_inverse] using hpos x hx
  · intro y hy
    have he : (rotation θ) '' sphere (d.center i) r = sphere (rotation θ (d.center i)) r := by
      ext y
      change y ∈ (rotation θ).toEquiv '' sphere (d.center i) r ↔ _
      rw [(rotation θ).toEquiv.image_eq_preimage]
      change dist ((rotation θ).symm y) (d.center i)=r ↔ dist y (rotation θ (d.center i))=r
      rw [← (rotation θ).dist_map ((rotation θ).symm y) (d.center i), (rotation θ).apply_symm_apply]
    change y ∈ sphere (rotation θ (d.center i)) r at hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact mem_image_of_mem _ (hsphere hx)
  · obtain ⟨inside,outside,hin,hout,hiae,hoae,hbound⟩ := hcollar
    have ht := Packet06AxialTraceCollar.rotated_trace_collar_general θ d.material d.supportRadius d.supportRadius
      d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization d.body (A i) (A i)
      d.body_open ho.measurableSet hs hpos inside outside hin hout hiae hoae B hbound
    exact ⟨transport θ inside,transport θ outside,ht⟩

theorem cyclic_collar {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B)
    (A : Fin N → Set Space) (hA : HasCollars d A) :
    HasCollars (cyclic d) (fun i => (placement 1 (by norm_num) 0) '' A i) := by
  intro i
  obtain ⟨ho,hs,hpos,hsphere,hcollar⟩ := hA i
  let h := placement 1 (by norm_num) 0
  refine ⟨h.isOpenMap _ ho,?_,?_,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    simpa [h,placement,Packet06PhysicalPlacement.point,mem_closedBall,dist_zero_right,
      Packet06CyclicRotation.rotate_norm] using hs hx
  · rintro y ⟨x,hx,rfl⟩
    change (placedCoefficient 1 0 d.material).value
      (VectorFourier.coordinateMap (Packet06CyclicTwiceGeneral.h x)) ≠ 0
    rw [Packet06CyclicTwiceGeneral.coefficient_image]
    exact hpos x hx
  · intro y hy
    have he : h '' sphere (d.center i) r = sphere (h (d.center i)) r := by
      ext w
      rw [h.image_eq_preimage]
      change dist (h.symm w) (d.center i)=r ↔ dist w (h (d.center i))=r
      have hh := Packet06PlanarProjection.point_distance_pair 1 (by norm_num) 0 (h.symm w) (d.center i)
      change dist (h (h.symm w)) (h (d.center i)) = _ at hh
      have hh' : dist w (h (d.center i)) = dist (h.symm w) (d.center i) := by simpa using hh
      rw [hh']
    change y ∈ sphere (h (d.center i)) r at hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact mem_image_of_mem _ (hsphere hx)
  · exact Packet06CyclicOneSidedGeneral.cyclic_one_sided_general d.material d.supportRadius d.supportRadius
      d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization d.body (A i) d.body_open ho hs hpos B hcollar

theorem affine_collar {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B)
    (A : Fin N → Set Space) (hA : HasCollars d A) :
    HasCollars (affine a d) (fun i => (placement 1 (by norm_num) a) '' A i) := by
  intro i
  obtain ⟨ho,hs,hpos,hsphere,hcollar⟩ := hA i
  let h := placement 1 (by norm_num) a
  refine ⟨h.isOpenMap _ ho,?_,?_,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    have hx' : ‖x‖ ≤ d.supportRadius := by simpa [mem_closedBall,dist_zero_right] using hs hx
    have hp : h x = a + Packet06CyclicRotation.rotate x := by
      change Packet06PhysicalPlacement.point 1 a x = _
      simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
    have hh := norm_add_le a (Packet06CyclicRotation.rotate x)
    rw [Packet06CyclicRotation.rotate_norm] at hh
    change h x ∈ closedBall 0 (d.supportRadius+‖a‖)
    rw [mem_closedBall,dist_zero_right,hp]
    linarith
  · rintro y ⟨x,hx,rfl⟩
    change (placedCoefficient 1 a d.material).value (VectorFourier.coordinateMap (h x)) ≠ 0
    rw [Packet06PlacedMaterialField.coefficient_value]
    have hb : Packet06CyclicRotation.unrotate ((1 : ℝ) • (h x-a))=x := by
      have hp : h x = a + Packet06CyclicRotation.rotate x := by
        change Packet06PhysicalPlacement.point 1 a x = _
        simp only [Packet06PhysicalPlacement.point,inv_one,one_smul]
      rw [hp]
      simp only [add_sub_cancel_left,one_smul,Packet06CyclicRotation.unrotate_rotate]
    exact fun hz => hpos x hx ((congrArg (fun y => d.material.value (VectorFourier.coordinateMap y)) hb).symm.trans hz)
  · intro y hy
    have he : h '' sphere (d.center i) r = sphere (h (d.center i)) r := by
      ext w
      rw [h.image_eq_preimage]
      change dist (h.symm w) (d.center i)=r ↔ dist w (h (d.center i))=r
      have hh := Packet06PlanarProjection.point_distance_pair 1 (by norm_num) a (h.symm w) (d.center i)
      change dist (h (h.symm w)) (h (d.center i)) = _ at hh
      have hh' : dist w (h (d.center i)) = dist (h.symm w) (d.center i) := by simpa using hh
      rw [hh']
    change y ∈ sphere (h (d.center i)) r at hy
    rw [← he] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    exact mem_image_of_mem _ (hsphere hx)
  · exact Packet06AffineOneSidedGeneral.affine_one_sided_general d.material d.supportRadius d.supportRadius
      d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization a d.body (A i) d.body_open ho hs hpos B hcollar

end OQ14.Packet06RigidCollar
#print axioms OQ14.Packet06RigidCollar.axial_collar
#print axioms OQ14.Packet06RigidCollar.cyclic_collar
#print axioms OQ14.Packet06RigidCollar.affine_collar

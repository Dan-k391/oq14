import Packet06RigidCollarFrame
import Packet06BoundedModalMaterial

/-! Literal dielectric values are preserved along the complete rigid frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidMaterialValues
open Metric Maxwell ModalAxialRotation Packet06RigidHotspotState Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06CyclicRotation
abbrev Space := Maxwell.Space

theorem axial_value {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B) (x : Space) :
    MaterialMaxwell.dielectric (axial θ d).material (ModalAxialRotation.rotation θ x) =
      MaterialMaxwell.dielectric d.material x := by
  change MaterialMaxwell.dielectric (Packet06AxialMaterialTransport.coefficient θ d.material) _ = _
  rw [Packet06AxialMaterialTransport.dielectric_value]
  simp [ModalAxialRotation.rotation,ModalAxialRotation.spatial_inverse]

theorem cyclic_value {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) (x : Space) :
    MaterialMaxwell.dielectric (cyclic d).material ((placement 1 (by norm_num) 0) x) =
      MaterialMaxwell.dielectric d.material x := by
  change MaterialMaxwell.dielectric (placedCoefficient 1 0 d.material) _ = _
  unfold MaterialMaxwell.dielectric
  change 1 + (placedCoefficient 1 0 d.material).value (VectorFourier.coordinateMap (Packet06CyclicTwiceGeneral.h x)) = _
  rw [Packet06CyclicTwiceGeneral.coefficient_image]

theorem affine_value {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B) (x : Space) :
    MaterialMaxwell.dielectric (affine a d).material ((placement 1 (by norm_num) a) x) =
      MaterialMaxwell.dielectric d.material x := by
  change MaterialMaxwell.dielectric (placedCoefficient 1 a d.material) _ = _
  rw [Packet06BoundedModalMaterial.placed_dielectric]
  have hp : (placement 1 (by norm_num) a) x = a + rotate x := by
    change Packet06PhysicalPlacement.point 1 a x = _
    simp [Packet06PhysicalPlacement.point]
  rw [hp]
  simp [unrotate_rotate]

theorem frame_value {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (x : Space) :
    MaterialMaxwell.dielectric (Packet06RigidHotspotFrame.transform θ φ a d).material
      (a + Packet07PlaneFrame.normalRotation θ φ x) = MaterialMaxwell.dielectric d.material x := by
  let h := placement 1 (by norm_num) 0
  let hA := placement 1 (by norm_num) a
  let d1 := cyclic d
  let d2 := axial φ d1
  let d3 := cyclic d2
  let d4 := cyclic d3
  let d5 := axial θ d4
  let d6 := cyclic d5
  let d7 := cyclic d6
  have hp : hA (h (h (ModalAxialRotation.rotation θ (h (h (ModalAxialRotation.rotation φ (h x))))))) =
      a + Packet07PlaneFrame.normalRotation θ φ x := by
    change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
      (Packet06PhysicalPlacement.point 1 0 (ModalAxialRotation.rotation θ
        (Packet06PhysicalPlacement.point 1 0 (Packet06PhysicalPlacement.point 1 0
          (ModalAxialRotation.rotation φ (Packet06PhysicalPlacement.point 1 0 x))))))) = _
    simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,
      Packet06RigidHotspotFrame.cyclic_thrice,Packet06RigidHotspotFrame.twice_rotate]
    rw [rotate_unrotate]
    rfl
  rw [← hp]
  change MaterialMaxwell.dielectric (affine a d7).material (hA (h (h (ModalAxialRotation.rotation θ
    (h (h (ModalAxialRotation.rotation φ (h x)))))))) = _
  rw [affine_value,cyclic_value,cyclic_value,axial_value,cyclic_value,cyclic_value,axial_value,cyclic_value]

end OQ14.Packet06RigidMaterialValues
#print axioms OQ14.Packet06RigidMaterialValues.axial_value
#print axioms OQ14.Packet06RigidMaterialValues.cyclic_value
#print axioms OQ14.Packet06RigidMaterialValues.affine_value
#print axioms OQ14.Packet06RigidMaterialValues.frame_value

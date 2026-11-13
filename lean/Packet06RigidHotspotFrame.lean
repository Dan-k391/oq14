import Packet06RigidHotspotAffine
import Packet07PlaneCoordinates
import Packet07DrivenInverseCyclic

/-! The exact Euler-plus-translation transport of a complete physical hotspot
state, with no relabeling of any of its fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06RigidHotspotFrame
open Set Metric Maxwell Packet06RigidHotspotState Packet06CyclicRotation Packet07PlaneFrame

def transform {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Maxwell.Space) (d : State N z r M B) : State N z r M B :=
  affine a (cyclic (cyclic (axial θ (cyclic (cyclic (axial φ (cyclic d)))))))

theorem cyclic_thrice (x : Maxwell.Space) : rotate (rotate (rotate x))=x := by
  ext i
  fin_cases i <;> simp [rotate,WeakCurl.previous]

theorem twice_rotate (x : Maxwell.Space) : rotate (rotate x)=unrotate x := by
  ext i
  fin_cases i <;> simp [rotate,unrotate,WeakCurl.previous,WeakCurl.next]

theorem frame_center {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Maxwell.Space)
    (d : State N z r M B) (i : Fin N) :
    (transform θ φ a d).center i = a + normalRotation θ φ (d.center i) := by
  change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
    (Packet06PhysicalPlacement.point 1 0 (ModalAxialRotation.rotation θ
      (Packet06PhysicalPlacement.point 1 0 (Packet06PhysicalPlacement.point 1 0
        (ModalAxialRotation.rotation φ (Packet06PhysicalPlacement.point 1 0 (d.center i)))))))) = _
  simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,cyclic_thrice,twice_rotate]
  rw [rotate_unrotate]
  rfl

theorem frame_plane {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Maxwell.Space)
    (d : State N z r M B) :
    (transform θ φ a d).plane = (fun x => a + normalRotation θ φ x) '' d.plane := by
  change (Packet06PlacementHomeomorph.placement 1 (by norm_num) a) ''
    ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
      ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
        ((ModalAxialRotation.rotation θ) ''
          ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
            ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
              ((ModalAxialRotation.rotation φ) ''
                ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) '' d.plane))))))) = _
  simp only [Set.image_image]
  have he : (fun x => (Packet06PlacementHomeomorph.placement 1 (by norm_num) a)
    ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
      ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
        ((ModalAxialRotation.rotation θ)
          ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
            ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
              ((ModalAxialRotation.rotation φ) ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) x)))))))) =
      (fun x => a + normalRotation θ φ x) := by
    funext x
    change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
      (Packet06PhysicalPlacement.point 1 0 (ModalAxialRotation.rotation θ
        (Packet06PhysicalPlacement.point 1 0 (Packet06PhysicalPlacement.point 1 0
          (ModalAxialRotation.rotation φ (Packet06PhysicalPlacement.point 1 0 x))))))) = _
    simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,cyclic_thrice,twice_rotate]
    rw [rotate_unrotate]
    rfl
  rw [he]

theorem frame_body {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Maxwell.Space)
    (d : State N z r M B) :
    (transform θ φ a d).body = (fun x => a + normalRotation θ φ x) '' d.body := by
  change (Packet06PlacementHomeomorph.placement 1 (by norm_num) a) ''
    ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
      ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
        ((ModalAxialRotation.rotation θ) ''
          ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
            ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) ''
              ((ModalAxialRotation.rotation φ) ''
                ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) '' d.body))))))) = _
  simp only [Set.image_image]
  have he : (fun x => (Packet06PlacementHomeomorph.placement 1 (by norm_num) a)
    ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
      ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
        ((ModalAxialRotation.rotation θ)
          ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
            ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0)
              ((ModalAxialRotation.rotation φ) ((Packet06PlacementHomeomorph.placement 1 (by norm_num) 0) x)))))))) =
      (fun x => a + normalRotation θ φ x) := by
    funext x
    change Packet06PhysicalPlacement.point 1 a (Packet06PhysicalPlacement.point 1 0
      (Packet06PhysicalPlacement.point 1 0 (ModalAxialRotation.rotation θ
        (Packet06PhysicalPlacement.point 1 0 (Packet06PhysicalPlacement.point 1 0
          (ModalAxialRotation.rotation φ (Packet06PhysicalPlacement.point 1 0 x))))))) = _
    simp only [Packet06PhysicalPlacement.point,inv_one,one_smul,zero_add,cyclic_thrice,twice_rotate]
    rw [rotate_unrotate]
    rfl
  rw [he]

end OQ14.Packet06RigidHotspotFrame
#print axioms OQ14.Packet06RigidHotspotFrame.cyclic_thrice
#print axioms OQ14.Packet06RigidHotspotFrame.twice_rotate
#print axioms OQ14.Packet06RigidHotspotFrame.frame_center
#print axioms OQ14.Packet06RigidHotspotFrame.frame_plane
#print axioms OQ14.Packet06RigidHotspotFrame.frame_body

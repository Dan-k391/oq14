import Packet07DrivenFrameMaxwell
import Packet07AffineMaxwell

/-! Frame rotation commutes with literal power-normalized affine placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenFrameAffine
open Maxwell ModalAxialRotation Packet07DrivenFrameMaxwell
abbrev Space := Maxwell.Space

theorem axial_affine (θ s : ℝ) (a : Space) (F : Field) :
    Packet07DrivenAxialPair.rotateField θ (Packet07AffineMaxwell.affineField s a F) =
      Packet07AffineMaxwell.affineField s (rotation θ a) (Packet07DrivenAxialPair.rotateField θ F) := by
  funext x i
  have hx : rotation (-θ) (s • (x-rotation θ a)) = s • (rotation (-θ) x-a) := by
    rw [map_smul,map_sub]
    change s • (rotation (-θ) x-spatial (-θ) (spatial θ a)) = _
    rw [spatial_inverse]
  fin_cases i <;> simp [Packet07DrivenAxialPair.rotateField,Packet07AffineMaxwell.affineField,
    FrequencyScalingMaxwell.scaleField_apply,vector,hx] <;> ring

theorem cyclic_affine (s : ℝ) (a : Space) (F : Field) :
    Packet06CyclicRotationMaxwell.rotateField (Packet07AffineMaxwell.affineField s a F) =
      Packet07AffineMaxwell.affineField s (Packet06CyclicRotation.rotation a) (Packet06CyclicRotationMaxwell.rotateField F) := by
  funext x i
  have hx : Packet06CyclicRotation.unrotate (s • (x-Packet06CyclicRotation.rotation a)) =
      s • (Packet06CyclicRotation.unrotate x-a) := by
    change Packet06CyclicRotation.rotation.symm (s • (x-Packet06CyclicRotation.rotation a)) = _
    rw [map_smul,map_sub,Packet06CyclicRotation.rotation.symm_apply_apply]
    rfl
  simp [Packet06CyclicRotationMaxwell.rotateField,Packet07AffineMaxwell.affineField,
    FrequencyScalingMaxwell.scaleField_apply,hx]

theorem inverse_cyclic_affine (s : ℝ) (a : Space) (F : Field) :
    Packet07DrivenInverseCyclic.inverseField (Packet07AffineMaxwell.affineField s a F) =
      Packet07AffineMaxwell.affineField s (Packet06CyclicRotation.rotation.symm a) (Packet07DrivenInverseCyclic.inverseField F) := by
  rw [←Packet07DrivenInverseCyclic.twice_field,cyclic_affine,cyclic_affine,
    Packet07DrivenInverseCyclic.twice_field]
  have he : Packet06CyclicRotation.rotation (Packet06CyclicRotation.rotation a)=Packet06CyclicRotation.rotation.symm a := by
    change Packet06CyclicRotation.rotate (Packet06CyclicRotation.rotate a)=Packet06CyclicRotation.unrotate a
    ext i
    fin_cases i <;> simp [Packet06CyclicRotation.rotation,Packet06CyclicRotation.rotate,
      Packet06CyclicRotation.unrotate,WeakCurl.previous,WeakCurl.next]
  rw [he]

theorem frame_affine (θ φ s : ℝ) (a : Space) (F : Field) :
    frameField θ φ (Packet07AffineMaxwell.affineField s a F) =
      Packet07AffineMaxwell.affineField s (Packet07PlaneFrame.normalRotation θ φ a) (frameField θ φ F) := by
  unfold frameField
  rw [cyclic_affine,axial_affine,inverse_cyclic_affine,axial_affine]
  rfl
end OQ14.Packet07DrivenFrameAffine
#print axioms OQ14.Packet07DrivenFrameAffine.axial_affine
#print axioms OQ14.Packet07DrivenFrameAffine.cyclic_affine
#print axioms OQ14.Packet07DrivenFrameAffine.inverse_cyclic_affine
#print axioms OQ14.Packet07DrivenFrameAffine.frame_affine

import Packet07DrivenRigidHotspot
import Packet07DrivenAffineGood
import Packet07DrivenFrameOutgoing

/-! Actual Maxwell fields and far fields under an arbitrary rigid frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenRigidFields
open Maxwell Packet07DrivenFrameMaxwell Packet07DrivenRigidHotspot Packet07DrivenRotatedOutgoing

theorem rigid_maxwell (θ φ k : ℝ) (a : Maxwell.Space) (ε : Maxwell.Space → ℝ) (E H : Field)
    (h : Good (k : ℂ) ε E H) :
    Packet06ComplexAffine.TestMaxwellC (k : ℂ)
      (fun x => ε ((Packet07PlaneFrame.normalRotation θ φ).symm (x-a)))
      (field θ φ a E) (field θ φ a H) := by
  exact Packet06ComplexAffine.translate _ _ _ _ (frame_good θ φ _ ε E H h).maxwell a

theorem rigid_outgoing (θ φ k : ℝ) (a c : Maxwell.Space) (F : Field) (A : Maxwell.Space → Vector)
    (h : OutAt k c F A) :
    OutAt k (placement θ φ a c) (field θ φ a F) (frameField θ φ A) := by
  intro v hv
  have hh := Packet07DrivenFrameOutgoing.frame_outgoing θ φ k c F A h v hv
  convert hh using 1; simp [placement,field,add_sub_cancel_left,add_comm,add_left_comm,add_assoc]
end OQ14.Packet07DrivenRigidFields
#print axioms OQ14.Packet07DrivenRigidFields.rigid_maxwell
#print axioms OQ14.Packet07DrivenRigidFields.rigid_outgoing

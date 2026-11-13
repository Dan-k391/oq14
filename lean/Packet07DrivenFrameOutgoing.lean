import Packet07DrivenRotatedOutgoing
import Packet07DrivenInverseCyclic

/-! Far-field limits in the exact arbitrary-plane frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenFrameOutgoing
open Maxwell Packet07DrivenRotatedOutgoing Packet07DrivenFrameMaxwell

theorem frame_outgoing (θ φ k : ℝ) (c : Space) (F : Field) (A : Space → Vector) (hF : OutAt k c F A) :
    OutAt k (Packet07PlaneFrame.normalRotation θ φ c) (frameField θ φ F) (frameField θ φ A) := by
  have h1 := cyclic_outgoing k c F A hF
  have h2 := axial_outgoing φ k _ _ _ h1
  have h3 := cyclic_outgoing k _ _ _ h2
  have h4 := cyclic_outgoing k _ _ _ h3
  have h5 := axial_outgoing θ k _ _ _ h4
  simpa only [Packet07PlaneFrame.normalRotation,LinearIsometryEquiv.trans_apply,
    Packet07DrivenInverseCyclic.twice_field,frameField,axialAmplitude,cyclicAmplitude,
    Packet07DrivenAxialPair.rotateField,Packet06CyclicRotationMaxwell.rotateField,
    Packet07DrivenInverseCyclic.inverseField,Packet07DrivenInverseCyclic.unrotate_twice,
    Packet06CyclicRotation.unrotate,Packet06CyclicRotation.rotate,WeakCurl.previous,WeakCurl.next] using h5
end OQ14.Packet07DrivenFrameOutgoing
#print axioms OQ14.Packet07DrivenFrameOutgoing.frame_outgoing

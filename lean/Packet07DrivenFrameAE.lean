import Packet07DrivenFrameMaxwell

/-! Almost-everywhere local field equality survives the exact frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenFrameAE
open MeasureTheory Maxwell ModalAxialRotation Packet07DrivenFrameMaxwell Packet07DrivenAxialPair
  Packet06CyclicRotation Packet06CyclicRotationMaxwell Packet07DrivenInverseCyclic

theorem axial (θ : ℝ) (P : Space → Prop) (F G : Field)
    (h : ∀ᵐ x ∂volume, P x → F x=G x) :
    ∀ᵐ y ∂volume, P (rotation (-θ) y) → rotateField θ F y=rotateField θ G y := by
  filter_upwards [(rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae h] with y hy hp
  exact congrArg (vector θ) (hy hp)

theorem cyclic (P : Space → Prop) (F G : Field)
    (h : ∀ᵐ x ∂volume, P x → F x=G x) :
    ∀ᵐ y ∂volume, P (unrotate y) →
      Packet06CyclicRotationMaxwell.rotateField F y=Packet06CyclicRotationMaxwell.rotateField G y := by
  filter_upwards [Packet06CyclicRotation.rotation.symm.measurePreserving.quasiMeasurePreserving.ae h] with y hy hp
  funext i
  exact congrFun (hy hp) _

theorem frame (θ φ : ℝ) (P : Space → Prop) (F G : Field)
    (h : ∀ᵐ x ∂volume, P x → F x=G x) :
    ∀ᵐ y ∂volume, P ((Packet07PlaneFrame.normalRotation θ φ).symm y) →
      frameField θ φ F y=frameField θ φ G y := by
  have h1 := cyclic P F G h
  have h2 := axial φ _ _ _ h1
  have h3 := cyclic _ _ _ h2
  have h4 := cyclic _ _ _ h3
  have h5 := axial θ _ _ _ h4
  exact h5
end OQ14.Packet07DrivenFrameAE
#print axioms OQ14.Packet07DrivenFrameAE.axial
#print axioms OQ14.Packet07DrivenFrameAE.cyclic
#print axioms OQ14.Packet07DrivenFrameAE.frame

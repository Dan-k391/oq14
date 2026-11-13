import Packet07DrivenFrameAE
import Packet07DrivenRigidFields

/-! The exterior almost-everywhere equality and vector addition survive placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenRigidAE
open MeasureTheory Maxwell Packet07DrivenFrameMaxwell Packet07DrivenFrameAE Packet07DrivenRigidHotspot

theorem field_add (θ φ : ℝ) (a : Maxwell.Space) (F G : Field) :
    field θ φ a (fun x => F x+G x) = fun x => field θ φ a F x+field θ φ a G x := by
  funext x i
  fin_cases i <;> simp [field,frameField,Packet07DrivenAxialPair.rotateField,
    Packet07DrivenInverseCyclic.inverseField,Packet06CyclicRotationMaxwell.rotateField,
    ModalAxialRotation.vector,WeakCurl.next,WeakCurl.previous] <;> ring

theorem field_ae (θ φ : ℝ) (a : Maxwell.Space) (P : Maxwell.Space → Prop) (F G : Field)
    (h : ∀ᵐ x ∂volume, P x → F x=G x) :
    ∀ᵐ y ∂volume, P ((Packet07PlaneFrame.normalRotation θ φ).symm (y-a)) →
      field θ φ a F y=field θ φ a G y := by
  have hh := (measurePreserving_add_right (volume : Measure Maxwell.Space) (-a)).quasiMeasurePreserving.ae
    (Packet07DrivenFrameAE.frame θ φ P F G h)
  simpa only [field,sub_eq_add_neg] using hh

theorem exterior_decomposition (θ φ : ℝ) (a : Maxwell.Space) (P : Maxwell.Space → Prop)
    (E I S : Field) (h : ∀ᵐ x ∂volume, P x → E x=I x+S x) :
    ∀ᵐ y ∂volume, P ((Packet07PlaneFrame.normalRotation θ φ).symm (y-a)) →
      field θ φ a E y=field θ φ a I y+field θ φ a S y := by
  have hh := field_ae θ φ a P E (fun x => I x+S x) h
  simpa only [field_add] using hh
end OQ14.Packet07DrivenRigidAE
#print axioms OQ14.Packet07DrivenRigidAE.field_add
#print axioms OQ14.Packet07DrivenRigidAE.field_ae
#print axioms OQ14.Packet07DrivenRigidAE.exterior_decomposition

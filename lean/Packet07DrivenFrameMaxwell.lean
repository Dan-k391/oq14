import Packet07DrivenInverseCyclic
import Packet07PlaneFrame

/-! The exact normal-reaching proper rotation transports genuine weak Maxwell fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenFrameMaxwell
open MeasureTheory Maxwell Packet06ComplexAffine Packet06CyclicRotation Packet06CyclicRotationMaxwell
  Packet07DrivenAxialPair Packet07DrivenAxialMaxwell Packet07DrivenRotationLocal Packet07DrivenInverseCyclic

structure Good (z : ℂ) (ε : Space → ℝ) (E H : Field) : Prop where
  electric_local : ∀ i, LocallyIntegrable (fun x => E x i)
  magnetic_local : ∀ i, LocallyIntegrable (fun x => H x i)
  dielectric_local : ∀ i, LocallyIntegrable (fun x => (ε x : ℂ)*E x i)
  maxwell : TestMaxwellC z ε E H

theorem axial_good (θ : ℝ) (z : ℂ) (ε : Space → ℝ) (E H : Field) (h : Good z ε E H) :
    Good z (fun x => ε (ModalAxialRotation.rotation (-θ) x)) (Packet07DrivenAxialPair.rotateField θ E)
      (Packet07DrivenAxialPair.rotateField θ H) := by
  refine ⟨axial_field_local θ E h.electric_local,axial_field_local θ H h.magnetic_local,?_,
    Packet07DrivenAxialMaxwell.complex_maxwell_rotate θ z ε E H h.electric_local h.magnetic_local h.dielectric_local h.maxwell⟩
  intro i
  have hh := axial_field_local θ (fun x j => (ε x : ℂ)*E x j) h.dielectric_local i
  simpa only [← dielectric_rotate] using hh

theorem cyclic_good (z : ℂ) (ε : Space → ℝ) (E H : Field) (h : Good z ε E H) :
    Good z (fun x => ε (unrotate x)) (Packet06CyclicRotationMaxwell.rotateField E)
      (Packet06CyclicRotationMaxwell.rotateField H) := by
  refine ⟨cyclic_field_local E h.electric_local,cyclic_field_local H h.magnetic_local,?_,
    Packet06CyclicRotationMaxwell.complex_maxwell_rotate z ε E H h.maxwell⟩
  intro i
  exact cyclic_field_local (fun x j => (ε x : ℂ)*E x j) h.dielectric_local i

theorem inverse_cyclic_good (z : ℂ) (ε : Space → ℝ) (E H : Field) (h : Good z ε E H) :
    Good z (fun x => ε (rotate x)) (inverseField E) (inverseField H) := by
  refine ⟨inverse_field_local E h.electric_local,inverse_field_local H h.magnetic_local,?_,
    complex_maxwell_inverse z ε E H h.maxwell⟩
  intro i
  exact inverse_field_local (fun x j => (ε x : ℂ)*E x j) h.dielectric_local i

def frameField (θ φ : ℝ) (F : Field) : Field :=
  Packet07DrivenAxialPair.rotateField θ (inverseField
    (Packet07DrivenAxialPair.rotateField φ (Packet06CyclicRotationMaxwell.rotateField F)))

theorem frame_good (θ φ : ℝ) (z : ℂ) (ε : Space → ℝ) (E H : Field) (h : Good z ε E H) :
    Good z (fun x => ε ((Packet07PlaneFrame.normalRotation θ φ).symm x))
      (frameField θ φ E) (frameField θ φ H) := by
  have hh := axial_good θ z _ _ _ (inverse_cyclic_good z _ _ _ (axial_good φ z _ _ _ (cyclic_good z ε E H h)))
  exact hh
end OQ14.Packet07DrivenFrameMaxwell
#print axioms OQ14.Packet07DrivenFrameMaxwell.axial_good
#print axioms OQ14.Packet07DrivenFrameMaxwell.cyclic_good
#print axioms OQ14.Packet07DrivenFrameMaxwell.inverse_cyclic_good
#print axioms OQ14.Packet07DrivenFrameMaxwell.frame_good

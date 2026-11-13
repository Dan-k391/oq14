import Packet07DrivenRotationLocal

/-! Inverse cyclic rotation covariance follows from two forward cyclic rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenInverseCyclic
open Maxwell Packet06CyclicRotation Packet06CyclicRotationMaxwell Packet06ComplexAffine

def inverseField (F : Field) : Field := fun x i => F (rotate x) (WeakCurl.next i)

theorem unrotate_twice (x : Space) : unrotate (unrotate x)=rotate x := by
  ext i
  fin_cases i <;> simp [rotate,unrotate,WeakCurl.next,WeakCurl.previous]

theorem twice_field (F : Field) : rotateField (rotateField F)=inverseField F := by
  funext x i
  fin_cases i <;> simp [rotateField,inverseField,unrotate_twice,WeakCurl.next,WeakCurl.previous]

theorem complex_maxwell_inverse (z : ℂ) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwellC z ε E H) :
    TestMaxwellC z (fun x => ε (rotate x)) (inverseField E) (inverseField H) := by
  have h := complex_maxwell_rotate z (fun x => ε (unrotate x)) (rotateField E) (rotateField H)
    (complex_maxwell_rotate z ε E H hM)
  simpa only [unrotate_twice,twice_field] using h

theorem inverse_field_local (F : Field) (hF : ∀ i, MeasureTheory.LocallyIntegrable (fun x => F x i)) :
    ∀ i, MeasureTheory.LocallyIntegrable (fun x => inverseField F x i) := by
  rw [←twice_field]
  exact Packet07DrivenRotationLocal.cyclic_field_local _ (Packet07DrivenRotationLocal.cyclic_field_local F hF)
end OQ14.Packet07DrivenInverseCyclic
#print axioms OQ14.Packet07DrivenInverseCyclic.unrotate_twice
#print axioms OQ14.Packet07DrivenInverseCyclic.twice_field
#print axioms OQ14.Packet07DrivenInverseCyclic.complex_maxwell_inverse
#print axioms OQ14.Packet07DrivenInverseCyclic.inverse_field_local

import Packet06CyclicRotationTests

/-! Exact proper-rotation covariance of complex-frequency weak Maxwell. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicRotationMaxwell
open MeasureTheory Maxwell DynamicSource MagneticResponse MaterialMaxwell Packet06CyclicRotation Packet06CyclicRotationTests Packet06ComplexAffine
open WeakCurl (next previous)

def rotateField (F : Field) : Field := fun x i => F (unrotate x) (previous i)

theorem rotateTest_partial_comm (f : Test) (j : Fin 3) :
    rotateTest (testPartial j f) = testPartial (previous j) (rotateTest f) := by
  apply Subtype.ext
  ext x
  rw [rotateTest_apply, rotateTest_partial]
  fin_cases j <;> rfl

theorem fieldPair_rotate (F : Field) (i : Fin 3) (f : Test) :
    fieldPair (rotateField F) i f = fieldPair F (previous i) (rotateTest f) := by
  exact pairing_rotate (fun x => F x (previous i)) f

theorem curlPair_rotate (F : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (rotateField F)) i f = curlPair (fieldPair F) (previous i) (rotateTest f) := by
  unfold curlPair
  rw [fieldPair_rotate, fieldPair_rotate, rotateTest_partial_comm, rotateTest_partial_comm]
  fin_cases i <;> rfl

theorem dielectric_pair_rotate (ε : Space → ℝ) (F : Field) (i : Fin 3) (f : Test) :
    (∫ x, (ε (unrotate x) : ℂ) * rotateField F x i * f.val x) =
      ∫ x, (ε x : ℂ) * F x (previous i) * (rotateTest f).val x := by
  exact pairing_rotate (fun x => (ε x : ℂ) * F x (previous i)) f

theorem complex_maxwell_rotate (z : ℂ) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwellC z ε E H) :
    TestMaxwellC z (fun x => ε (unrotate x)) (rotateField E) (rotateField H) := by
  intro i f
  have h := hM (previous i) (rotateTest f)
  constructor
  · rw [curlPair_rotate, fieldPair_rotate]
    exact h.1
  · rw [curlPair_rotate, dielectric_pair_rotate]
    exact h.2

end OQ14.Packet06CyclicRotationMaxwell
#print axioms OQ14.Packet06CyclicRotationMaxwell.rotateTest_partial_comm
#print axioms OQ14.Packet06CyclicRotationMaxwell.fieldPair_rotate
#print axioms OQ14.Packet06CyclicRotationMaxwell.curlPair_rotate
#print axioms OQ14.Packet06CyclicRotationMaxwell.dielectric_pair_rotate
#print axioms OQ14.Packet06CyclicRotationMaxwell.complex_maxwell_rotate

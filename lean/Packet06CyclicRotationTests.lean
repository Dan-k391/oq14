import Packet06CyclicRotation

/-! Compact tests and derivative transport for the proper Cartesian rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicRotationTests
open MeasureTheory Maxwell DynamicSource Packet06CyclicRotation
open WeakCurl (next previous)

def rotateTest (f : Test) : Test :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rotation.toContinuousLinearEquiv f.val,
    f.property.comp_homeomorph rotation.toHomeomorph⟩

theorem rotateTest_apply (f : Test) (x : Space) : (rotateTest f).val x = f.val (rotate x) := rfl

theorem rotateTest_partial (f : Test) (j : Fin 3) (x : Space) :
    (testPartial j (rotateTest f)).val x = (testPartial (next j) f).val (rotate x) := by
  change GradientProjection.pderivative j (rotateTest f).val x =
    GradientProjection.pderivative (next j) f.val (rotate x)
  rw [GradientProjection.pderivative_apply, GradientProjection.pderivative_apply]
  have hf : (fun y : Space => (rotateTest f).val y) = fun y => f.val (rotate y) := rfl
  change dcoord (fun y : Space => (rotateTest f).val y) x j = _
  rw [hf]
  have hd := f.val.differentiableAt.hasFDerivAt.comp x rotation.toContinuousLinearEquiv.hasFDerivAt
  change HasFDerivAt (fun y => f.val (rotate y)) _ x at hd
  unfold dcoord
  rw [hd.fderiv]
  change fderiv ℝ f.val (rotate x) (rotate (basis j)) = _
  rw [show rotate (basis j) = basis (next j) from rotation_basis j]

theorem pairing_rotate (F : Space → ℂ) (f : Test) :
    (∫ x, F (unrotate x) * f.val x) = ∫ x, F x * (rotateTest f).val x := by
  have hh := rotation.measurePreserving.integral_comp rotation.toHomeomorph.measurableEmbedding
    (fun x : Space => F (unrotate x) * f.val x)
  simpa [Function.comp_apply, rotation, unrotate_rotate, rotateTest_apply] using hh.symm

end OQ14.Packet06CyclicRotationTests
#print axioms OQ14.Packet06CyclicRotationTests.rotateTest_apply
#print axioms OQ14.Packet06CyclicRotationTests.rotateTest_partial
#print axioms OQ14.Packet06CyclicRotationTests.pairing_rotate

import Packet06CyclicRotationTests
import WeakAnnularMoment

/-! Compact test and derivative transport for arbitrary proper axial rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenAxialTests
open MeasureTheory Maxwell DynamicSource ModalAxialRotation

def rotateTest (θ : ℝ) (f : Test) : Test :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rotation θ).toContinuousLinearEquiv f.val,
    f.property.comp_homeomorph (rotation θ).toHomeomorph⟩

theorem rotateTest_apply (θ : ℝ) (f : Test) (x : Space) : (rotateTest θ f).val x=f.val (rotation θ x) := rfl

theorem rotation_basis_zero (θ : ℝ) : rotation θ (basis 0) = Real.cos θ • basis 0 + Real.sin θ • basis 1 := by
  ext i
  fin_cases i <;> simp [rotation,spatial,basis,EuclideanSpace.single_apply,PiLp.add_apply,PiLp.smul_apply]

theorem rotation_basis_one (θ : ℝ) : rotation θ (basis 1) = (-Real.sin θ) • basis 0 + Real.cos θ • basis 1 := by
  ext i
  fin_cases i <;> simp [rotation,spatial,basis,EuclideanSpace.single_apply,PiLp.add_apply,PiLp.smul_apply]

theorem rotation_basis_two (θ : ℝ) : rotation θ (basis 2) = basis 2 := by
  ext i
  fin_cases i <;> simp [rotation,spatial,basis,EuclideanSpace.single_apply]

theorem rotateTest_partial_zero (θ : ℝ) (f : Test) (x : Space) :
    (testPartial 0 (rotateTest θ f)).val x = (Real.cos θ : ℂ)*(testPartial 0 f).val (rotation θ x) +
      (Real.sin θ : ℂ)*(testPartial 1 f).val (rotation θ x) := by
  change dcoord (fun y => f.val (rotation θ y)) x 0 = _
  have hd := f.val.differentiableAt.hasFDerivAt.comp x (rotation θ).toContinuousLinearEquiv.hasFDerivAt
  change HasFDerivAt (fun y => f.val (rotation θ y)) _ x at hd
  unfold dcoord
  rw [hd.fderiv]
  change fderiv ℝ f.val (rotation θ x) (rotation θ (basis 0)) = _
  rw [rotation_basis_zero,map_add,map_smul,map_smul]
  simp only [smul_eq_mul,Complex.real_smul,GradientProjection.pderivative_apply,testPartial]
  rfl

theorem rotateTest_partial_one (θ : ℝ) (f : Test) (x : Space) :
    (testPartial 1 (rotateTest θ f)).val x = -(Real.sin θ : ℂ)*(testPartial 0 f).val (rotation θ x) +
      (Real.cos θ : ℂ)*(testPartial 1 f).val (rotation θ x) := by
  change dcoord (fun y => f.val (rotation θ y)) x 1 = _
  have hd := f.val.differentiableAt.hasFDerivAt.comp x (rotation θ).toContinuousLinearEquiv.hasFDerivAt
  change HasFDerivAt (fun y => f.val (rotation θ y)) _ x at hd
  unfold dcoord
  rw [hd.fderiv]
  change fderiv ℝ f.val (rotation θ x) (rotation θ (basis 1)) = _
  rw [rotation_basis_one,map_add,map_smul,map_smul]
  simp only [smul_eq_mul,Complex.real_smul,Complex.ofReal_neg,GradientProjection.pderivative_apply,testPartial]
  rfl

theorem rotateTest_partial_two (θ : ℝ) (f : Test) (x : Space) :
    (testPartial 2 (rotateTest θ f)).val x = (testPartial 2 f).val (rotation θ x) := by
  change dcoord (fun y => f.val (rotation θ y)) x 2 = _
  have hd := f.val.differentiableAt.hasFDerivAt.comp x (rotation θ).toContinuousLinearEquiv.hasFDerivAt
  change HasFDerivAt (fun y => f.val (rotation θ y)) _ x at hd
  unfold dcoord
  rw [hd.fderiv]
  change fderiv ℝ f.val (rotation θ x) (rotation θ (basis 2)) = _
  rw [rotation_basis_two]
  rfl

theorem pairing_rotate (θ : ℝ) (F : Space → ℂ) (f : Test) :
    (∫ x, F (rotation (-θ) x)*f.val x)=∫ x, F x*(rotateTest θ f).val x := by
  have hh := (rotation θ).measurePreserving.integral_comp (rotation θ).toHomeomorph.measurableEmbedding
    (fun x : Space => F (rotation (-θ) x)*f.val x)
  simpa [Function.comp_apply,rotateTest_apply,rotation,spatial_inverse] using hh.symm
end OQ14.Packet07DrivenAxialTests
#print axioms OQ14.Packet07DrivenAxialTests.rotateTest_apply
#print axioms OQ14.Packet07DrivenAxialTests.rotation_basis_zero
#print axioms OQ14.Packet07DrivenAxialTests.rotation_basis_one
#print axioms OQ14.Packet07DrivenAxialTests.rotation_basis_two
#print axioms OQ14.Packet07DrivenAxialTests.rotateTest_partial_zero
#print axioms OQ14.Packet07DrivenAxialTests.rotateTest_partial_one
#print axioms OQ14.Packet07DrivenAxialTests.rotateTest_partial_two
#print axioms OQ14.Packet07DrivenAxialTests.pairing_rotate

import Packet06ComplexPotentialPair
import ComplexMagneticAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexHessian
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

def hessianDifference (z : ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  ComplexDynamicKernel.remainder z x i j - z^2 * ComplexGreenKernel.phi z x * (if i = j then 1 else 0)

theorem gradient_differentiable (z : ℂ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => ComplexGreenKernel.phiGradient z y j) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd := ComplexGreenKernel.radialD_hasDerivAt z ‖x‖ hr
  have hdiff : DifferentiableAt ℝ (fun y : Space => ComplexGreenKernel.radialD z ‖y‖) x :=
    (hd.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  have hu := GreenKernel.unitCoordinate_differentiableAt j x hx
  have heq : (fun y => ComplexGreenKernel.phiGradient z y j) =
      fun y => (1 / (4 * Real.pi) : ℂ) * (ComplexGreenKernel.radialD z ‖y‖ * GreenKernel.unitCoordinate j y) := by
    funext y
    simp [ComplexGreenKernel.phiGradient, GreenKernel.unitCoordinate, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [heq]
  exact (differentiableAt_const _).mul (hdiff.mul hu)

theorem hessian_weak_partial (z : ℂ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, hessianDifference z x i j * φ x) =
      -(∫ x, ComplexMagneticAnalytic.gradientDifference z x j * dcoord φ x i) := by
  apply PointSingularity.weak_partial i (fun x => ComplexMagneticAnalytic.gradientDifference z x j)
    (fun x => hessianDifference z x i j)
  · intro x hx
    exact (gradient_differentiable z x hx j).sub (gradient_differentiable 0 x hx j)
  · intro x hx
    simp only [ComplexMagneticAnalytic.gradientDifference, dcoord, fderiv_sub
      (gradient_differentiable z x hx j) (gradient_differentiable 0 x hx j), ContinuousLinearMap.sub_apply]
    change dcoord (fun y => ComplexGreenKernel.phiGradient z y j) x i - dcoord (fun y => ComplexGreenKernel.phiGradient 0 y j) x i = _
    rw [ComplexGreenKernel.phiGradient_partial z x hx i j, ComplexGreenKernel.phiGradient_partial 0 x hx i j]
    simp only [hessianDifference, ComplexDynamicKernel.remainder, ComplexDynamicKernel.dyadic]
    ring
  · exact (ComplexMagneticLocal.gradient_locallyIntegrable z j).sub
      (ComplexMagneticLocal.gradient_locallyIntegrable 0 j)
  · have hl := (Packet06ComplexScalarKernel.phi_locallyIntegrable z).smul (z^2 * (if i = j then 1 else 0))
    have hl' : LocallyIntegrable (fun x => z^2 * ComplexGreenKernel.phi z x * (if i = j then 1 else 0)) := by
      convert hl using 1
      ext x
      simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    exact (ComplexDynamicKernel.remainder_locallyIntegrable z i j).sub hl'
  · exact hφ
  · exact hc
theorem hessian_locallyIntegrable (z : ℂ) (i j : Fin 3) :
    LocallyIntegrable (fun x => hessianDifference z x i j) := by
  have hl := (Packet06ComplexScalarKernel.phi_locallyIntegrable z).smul (z^2 * (if i = j then 1 else 0))
  have hl' : LocallyIntegrable (fun x => z^2 * ComplexGreenKernel.phi z x * (if i = j then 1 else 0)) := by
    convert hl using 1
    ext x
    simp [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  exact (ComplexDynamicKernel.remainder_locallyIntegrable z i j).sub hl'

theorem hessian_pairing (z : ℂ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    (∫ x, response (fun y => hessianDifference z y i j) ρ x * f.val x) =
      -(∫ x, response (fun y => ComplexMagneticAnalytic.gradientDifference z y j) ρ x * (testPartial i f).val x) := by
  rw [response_pairing _ ρ (hessian_locallyIntegrable z i j) hρ hc f]
  unfold ComplexMagneticAnalytic.gradientDifference
  have hloc : LocallyIntegrable (fun y => ComplexGreenKernel.phiGradient z y j - ComplexGreenKernel.phiGradient 0 y j) :=
    (ComplexMagneticLocal.gradient_locallyIntegrable z j).sub (ComplexMagneticLocal.gradient_locallyIntegrable 0 j)
  rw [response_pairing _ ρ hloc hρ hc (testPartial i f)]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [← translated_pairing (fun x => hessianDifference z x i j) y f]
  rw [hessian_weak_partial z i j (translate y f).val ((translate y f).val.smooth 1) (translate y f).property]
  change ρ y * -(∫ x, ComplexMagneticAnalytic.gradientDifference z x j * dcoord (translate y f).val x i) =
    -(ρ y * ∫ x, ComplexMagneticAnalytic.gradientDifference z (x-y) j * (testPartial i f).val x)
  rw [← translated_pairing (fun x => ComplexMagneticAnalytic.gradientDifference z x j) y (testPartial i f)]
  rw [translate_partial]
  simp only [testPartial, GradientProjection.pderivative_apply, mul_neg]
#print axioms OQ14.Packet06ComplexHessian.gradient_differentiable
#print axioms OQ14.Packet06ComplexHessian.hessian_weak_partial
#print axioms OQ14.Packet06ComplexHessian.hessian_locallyIntegrable
#print axioms OQ14.Packet06ComplexHessian.hessian_pairing
end OQ14.Packet06ComplexHessian

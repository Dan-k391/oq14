import Packet06ResponseLinear
import Packet05ComplexCorrectionRegularity

/-! The locally square-integrable dynamic Hessian is the actual weak
derivative of the difference of complex and static gradient responses. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ComplexCorrectionWeakHessian
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

theorem dynamic_hessian_weak_pairing (z : ℂ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    (∫ x, response (fun y => Packet06ComplexHessian.hessianDifference z y i j) ρ x * f.val x) =
      -(∫ x, response (fun y => ComplexGreenKernel.phiGradient z y j) ρ x * (testPartial i f).val x) +
       (∫ x, response (fun y => ComplexGreenKernel.phiGradient 0 y j) ρ x * (testPartial i f).val x) := by
  have h := Packet06ComplexHessian.hessian_pairing z ρ hρ hc i j f
  unfold ComplexMagneticAnalytic.gradientDifference at h
  rw [Packet06ResponseLinear.pairing_sub _ _ ρ
    (ComplexMagneticLocal.gradient_locallyIntegrable z j)
    (ComplexMagneticLocal.gradient_locallyIntegrable 0 j) hρ hc (testPartial i f)] at h
  linear_combination h

end OQ14.Packet05ComplexCorrectionWeakHessian
#print axioms OQ14.Packet05ComplexCorrectionWeakHessian.dynamic_hessian_weak_pairing

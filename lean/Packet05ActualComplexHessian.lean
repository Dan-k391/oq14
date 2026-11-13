import Packet05ActualStaticGradient

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ActualComplexHessian
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.Packet05ActualStaticGradient OQ14.Packet05ComplexCorrectionWeakHessian

theorem actual_complex_hessian_pairing (z : ℂ) (F : NewtonL2.ScalarL2) (ρ : Space → ℂ)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (i j : Fin 3) (f : Test) :
    (∫ x, NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f.val x) +
    (∫ x, response (fun y => Packet06ComplexHessian.hessianDifference z y i j) ρ x * f.val x) =
      -(∫ x, response (fun y => ComplexGreenKernel.phiGradient z y j) ρ x *
        (testPartial i f).val x) := by
  have hs := actual_static_gradient_pairing F ρ hF hρ hc i j f
  have hd := dynamic_hessian_weak_pairing z ρ hρ hc i j f
  linear_combination hs + hd

end OQ14.Packet05ActualComplexHessian
#print axioms OQ14.Packet05ActualComplexHessian.actual_complex_hessian_pairing

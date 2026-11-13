import Packet05StaticGradientPairing

/-! The full complex scalar Green Hessian consists of the static L² Newton
operator and the locally L² dynamic response, with the actual weak pairing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ComplexFullHessian
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.Packet05StaticGradientPairing OQ14.Packet05ComplexCorrectionWeakHessian

theorem complex_hessian_weak_pairing (z : ℂ) (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hc : HasCompactSupport (F : Space → ℂ))
    (i j : Fin 3) (f : Test) :
    (∫ x, NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f.val x) +
    (∫ x, response (fun y => Packet06ComplexHessian.hessianDifference z y i j) (F : Space → ℂ) x * f.val x) =
      -(∫ x, response (fun y => ComplexGreenKernel.phiGradient z y j) (F : Space → ℂ) x *
        (testPartial i f).val x) := by
  have hs := static_gradient_pairing F hF hc i j f
  have hd := dynamic_hessian_weak_pairing z (F : Space → ℂ) hF hc i j f
  linear_combination hs + hd

end OQ14.Packet05ComplexFullHessian
#print axioms OQ14.Packet05ComplexFullHessian.complex_hessian_weak_pairing

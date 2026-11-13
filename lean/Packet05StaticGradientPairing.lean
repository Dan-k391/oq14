import Packet05ScalarNewtonPairing

/-! Identify the actual static Newton Hessian against the first gradient response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05StaticGradientPairing
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.Packet06ComplexPotentialPair OQ14.Packet05ScalarNewtonPairing
open scoped SchwartzMap

theorem static_gradient_pairing (F : NewtonL2.ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hc : HasCompactSupport (F : Space → ℂ))
    (i j : Fin 3) (f : Test) :
    (∫ x, NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f.val x) =
      -(∫ x, response (fun y => ComplexGreenKernel.phiGradient 0 y j) (F : Space → ℂ) x *
        (testPartial i f).val x) := by
  rw [scalar_newton_hessian_pairing F hF i j f.val,
    gradient_pairing 0 (F : Space → ℂ) hF hc j (testPartial i f), neg_neg]
  unfold NewtonConvolution.weakConvolution potentialPair Packet06ComplexPotentialPair.scalarPair
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  rw [NewtonHessian.weakHessian]
  simp only [ComplexGreenKernel.phi_ofReal, Complex.ofReal_zero, translate_partial,
    testPartial, GradientProjection.pderivative_apply]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  change dcoord (fun t => dcoord (NewtonConvolution.translate y f.val) t j) x i =
    (NewtonConvolution.translate y (GradientProjection.pderivative j (GradientProjection.pderivative i f.val))) x
  rw [← NewtonConvolution.translate_pderivative, ← NewtonConvolution.translate_pderivative]
  exact Maxwell.partial_comm ((NewtonConvolution.translate y f.val).smooth 2) x i j

end OQ14.Packet05StaticGradientPairing
#print axioms OQ14.Packet05StaticGradientPairing.static_gradient_pairing

import Packet05GreenSourceAE

/-! Static Newton Hessian pairing for an arbitrary actual representative of
the L² source, with compact support imposed on that actual representative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ActualStaticGradient
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.Packet06ComplexPotentialPair OQ14.Packet05ScalarNewtonPairing
open scoped SchwartzMap

theorem actual_static_gradient_pairing (F : NewtonL2.ScalarL2) (ρ : Space → ℂ)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (i j : Fin 3) (f : Test) :
    (∫ x, NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (Packet05ScalarNewtonEmbedding.scalarSource F j)) i x * f.val x) =
      -(∫ x, response (fun y => ComplexGreenKernel.phiGradient 0 y j) ρ x *
        (testPartial i f).val x) := by
  have hFi : Integrable (F : Space → ℂ) := hρ.congr hF.symm
  rw [scalar_newton_hessian_pairing F hFi i j f.val,
    gradient_pairing 0 ρ hρ hc j (testPartial i f), neg_neg]
  unfold NewtonConvolution.weakConvolution potentialPair Packet06ComplexPotentialPair.scalarPair
  apply integral_congr_ae
  filter_upwards [hF] with y hy
  rw [hy]
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

end OQ14.Packet05ActualStaticGradient
#print axioms OQ14.Packet05ActualStaticGradient.actual_static_gradient_pairing

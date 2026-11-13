import Packet06ComplexHessian
import LocalConvolution

/-! Local L² control of the actual complex-frequency scalar-kernel derivatives.
The Hessian difference is the regular dynamic part; the static Newton Hessian
is treated separately as a Fourier multiplier. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ComplexCorrectionRegularity
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

theorem gradient_response_memLp_ball (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (j : Fin 3) :
    MemLp (response (fun y => ComplexGreenKernel.phiGradient z y j) ρ) 2
      (volume.restrict (closedBall 0 R)) :=
  LocalConvolution.response_memLp_ball _ (ComplexMagneticLocal.gradient_locallyIntegrable z j)
    ρ hρ F hF R S hc

theorem dynamic_hessian_response_memLp_ball (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (i j : Fin 3) :
    MemLp (response (fun y => Packet06ComplexHessian.hessianDifference z y i j) ρ) 2
      (volume.restrict (closedBall 0 R)) :=
  LocalConvolution.response_memLp_ball _ (Packet06ComplexHessian.hessian_locallyIntegrable z i j)
    ρ hρ F hF R S hc

end OQ14.Packet05ComplexCorrectionRegularity
#print axioms OQ14.Packet05ComplexCorrectionRegularity.gradient_response_memLp_ball
#print axioms OQ14.Packet05ComplexCorrectionRegularity.dynamic_hessian_response_memLp_ball

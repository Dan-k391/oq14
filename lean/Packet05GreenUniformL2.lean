import Packet05ActualGraphForcing

/-! Fixed-chart linear L² bounds for the actual Green responses. These
operators are independent of the source and hence uniform over mode families. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GreenUniformL2
open MeasureTheory Metric OQ14.Maxwell OQ14.KernelConvolution

theorem local_green_operator_bound (q ρ : Space → ℂ) (hq : LocallyIntegrable q volume)
    (R S : ℝ) (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y = 0) :
    ∃ U : NewtonL2.ScalarL2,
      (∀ᵐ x ∂volume, x ∈ closedBall 0 R → U x = response q ρ x) ∧
      ‖U‖ ≤ ‖LocalConvolution.operator q hq (R+S)‖ * ‖F‖ := by
  refine ⟨LocalConvolution.operator q hq (R+S) F, ?_, ?_⟩
  · exact LocalConvolution.operator_ae_on_ball q hq ρ hρ F hF R S hs
  · exact ContinuousLinearMap.le_opNorm _ _

theorem gradient_uniform_l2 (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (j : Fin 3) :
    ∃ U : NewtonL2.ScalarL2,
      (∀ᵐ x ∂volume, x ∈ closedBall 0 R →
        U x = response (fun y => ComplexGreenKernel.phiGradient z y j) ρ x) ∧
      ‖U‖ ≤ ‖LocalConvolution.operator _ (ComplexMagneticLocal.gradient_locallyIntegrable z j) (R+S)‖ * ‖F‖ :=
  local_green_operator_bound _ ρ (ComplexMagneticLocal.gradient_locallyIntegrable z j) R S F hρ hF hs

theorem dynamic_hessian_uniform_l2 (z : ℂ) (R S : ℝ) (F : NewtonL2.ScalarL2)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (i j : Fin 3) :
    ∃ U : NewtonL2.ScalarL2,
      (∀ᵐ x ∂volume, x ∈ closedBall 0 R →
        U x = response (fun y => Packet06ComplexHessian.hessianDifference z y i j) ρ x) ∧
      ‖U‖ ≤ ‖LocalConvolution.operator _ (Packet06ComplexHessian.hessian_locallyIntegrable z i j) (R+S)‖ * ‖F‖ :=
  local_green_operator_bound _ ρ (Packet06ComplexHessian.hessian_locallyIntegrable z i j) R S F hρ hF hs

end OQ14.Packet05GreenUniformL2
#print axioms OQ14.Packet05GreenUniformL2.local_green_operator_bound
#print axioms OQ14.Packet05GreenUniformL2.gradient_uniform_l2
#print axioms OQ14.Packet05GreenUniformL2.dynamic_hessian_uniform_l2

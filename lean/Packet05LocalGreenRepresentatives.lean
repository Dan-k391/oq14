import Packet05ComplexFullHessian
import Packet05RegionalPartial

/-! Canonical global L² representatives of the actual scalar Green responses
on any prescribed closed ball. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05LocalGreenRepresentatives
open MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.Packet05ComplexCorrectionRegularity

def ballRepresentative (R : ℝ) (f : Space → ℂ)
    (hf : MemLp f 2 (volume.restrict (closedBall 0 R))) : NewtonL2.ScalarL2 :=
  ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr hf).toLp
    ((closedBall 0 R).indicator f)

theorem ballRepresentative_ae (R : ℝ) (f : Space → ℂ)
    (hf : MemLp f 2 (volume.restrict (closedBall 0 R))) :
    ∀ᵐ x ∂volume, x ∈ closedBall 0 R → ballRepresentative R f hf x = f x := by
  filter_upwards [((memLp_indicator_iff_restrict measurableSet_closedBall).mpr hf).coeFn_toLp] with x hx hR
  simpa [ballRepresentative, Set.indicator_of_mem hR] using hx

def gradientRepresentative (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (j : Fin 3) : NewtonL2.ScalarL2 :=
  ballRepresentative R _ (gradient_response_memLp_ball z R S ρ F hρ hc hF j)

def dynamicHessianRepresentative (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (i j : Fin 3) : NewtonL2.ScalarL2 :=
  ballRepresentative R _ (dynamic_hessian_response_memLp_ball z R S ρ F hρ hc hF i j)

end OQ14.Packet05LocalGreenRepresentatives
#print axioms OQ14.Packet05LocalGreenRepresentatives.ballRepresentative_ae

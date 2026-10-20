import LocalConvolution
import MagneticResponse

/-! # Actual local L2 regularity of the magnetic source response -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MagneticLocal

open MeasureTheory Metric OQ14.Maxwell
open OQ14.WeakCurl (next previous)

theorem gradient_response_memLp_ball (k R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i j : Fin 3) :
    MemLp (KernelConvolution.response (fun z => GreenKernel.phiGradient k z i) (ρ j)) 2
      (volume.restrict (closedBall 0 R)) :=
  LocalConvolution.response_memLp_ball (fun z => GreenKernel.phiGradient k z i)
    (KernelGradient.gradient_locallyIntegrable k i) (ρ j) (hρ j)
    (NewtonL2.physicalCoordinate F j) (hF j) R S (hc j)

theorem magnetic_memLp_ball (k R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) :
    MemLp (fun x => MagneticResponse.magnetic k ρ x i) 2
      (volume.restrict (closedBall 0 R)) := by
  have h1 := gradient_response_memLp_ball k R S F ρ hρ hc hF (next i) (previous i)
  have h2 := gradient_response_memLp_ball k R S F ρ hρ hc hF (previous i) (next i)
  exact (h1.sub h2).const_mul (-(Complex.I * (k : ℂ)))

theorem magnetic_locallyIntegrable (k S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) : LocallyIntegrable (fun x => MagneticResponse.magnetic k ρ x i) := by
  have hh (j l : Fin 3) := LocalConvolution.response_locallyIntegrable
    (fun z => GreenKernel.phiGradient k z j) (KernelGradient.gradient_locallyIntegrable k j)
    (ρ l) (hρ l) (NewtonL2.physicalCoordinate F l) (hF l) S (hc l)
  exact ((hh (next i) (previous i)).sub (hh (previous i) (next i))).smul
    (-(Complex.I * (k : ℂ)))

end OQ14.MagneticLocal

#print axioms OQ14.MagneticLocal.gradient_response_memLp_ball
#print axioms OQ14.MagneticLocal.magnetic_memLp_ball
#print axioms OQ14.MagneticLocal.magnetic_locallyIntegrable

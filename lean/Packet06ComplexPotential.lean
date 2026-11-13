import Packet06ComplexScalarPotential
import ElectricPotentialDecomposition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexPotential
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

def potential (z : ℂ) (ρ : Fin 3 → Space → ℂ) (x : Space) : ℂ :=
  ∑ j : Fin 3, response (fun y => ComplexGreenKernel.phiGradient z y j) (ρ j) x

def correction (z : ℂ) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x i => z^2 * response (ComplexGreenKernel.phi z) (ρ i) x

theorem phi_weak_partial (z : ℂ) (j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, ComplexGreenKernel.phiGradient z x j * φ x) =
      -(∫ x, ComplexGreenKernel.phi z x * dcoord φ x j) :=
  PointSingularity.weak_partial j (ComplexGreenKernel.phi z) (fun x => ComplexGreenKernel.phiGradient z x j)
    (fun x hx => (ComplexGreenKernel.phi_contDiffAt z x hx).differentiableAt (by simp))
    (fun x hx => ComplexGreenKernel.phi_partial z x hx j)
    (Packet06ComplexScalarKernel.phi_locallyIntegrable z) (ComplexMagneticLocal.gradient_locallyIntegrable z j) φ hφ hc

theorem potential_memLp_ball (z : ℂ) (R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) :
    MemLp (potential z ρ) 2 (volume.restrict (closedBall 0 R)) := by
  apply memLp_finset_sum
  intro j _
  exact LocalConvolution.response_memLp_ball _ (ComplexMagneticLocal.gradient_locallyIntegrable z j)
    (ρ j) (hρ j) (NewtonL2.physicalCoordinate F j) (hF j) R S (hc j)

theorem correction_continuous (z : ℂ) (S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    Continuous (fun x => correction z ρ x i) :=
  continuous_const.mul (Packet06ComplexScalarPotential.response_continuous z S (ρ i)
    (NewtonL2.physicalCoordinate F i) (hF i) (hc i))

theorem correction_memLp_ball (z : ℂ) (R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    MemLp (fun x => correction z ρ x i) 2 (volume.restrict (closedBall 0 R)) :=
  (LocalConvolution.response_memLp_ball _ (Packet06ComplexScalarKernel.phi_locallyIntegrable z)
    (ρ i) (hρ i) (NewtonL2.physicalCoordinate F i) (hF i) R S (hc i)).const_mul (z^2)
#print axioms OQ14.Packet06ComplexPotential.phi_weak_partial
#print axioms OQ14.Packet06ComplexPotential.potential_memLp_ball
#print axioms OQ14.Packet06ComplexPotential.correction_continuous
#print axioms OQ14.Packet06ComplexPotential.correction_memLp_ball
end OQ14.Packet06ComplexPotential

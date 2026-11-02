import Packet01PoloidalCoefficients
import Packet01Monopole

/-! Complete Packet 01 endpoint for the actual electric response of a sphere-kernel vector. -/
noncomputable section
set_option autoImplicit false

namespace OQ14.Packet01CoefficientChain
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentCoupling OQ14.ComplexKernelResponse

theorem actual_electric_coefficients
    (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    (∀ p : Poly, ∀ l : ℕ, p.IsHomogeneous (l+1) →
      HarmonicPolynomial.formalLaplacian p = 0 →
      ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
        ((r : ℂ)^2 * ComplexKernelDebye.radialCoefficient n hn z u p r =
          c * RadialOriginSelection.regular (l+1) (z*n) r) ∧
        ((∫ ω : Sphere, ∑ j : Fin 3,
          response (ModalWeightedMode.coefficient n hn) z 1 u
            (VectorFourier.coordinateMap (r • (ω : Space))) j *
            (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω) ∂angularMeasure) =
          c * RadialOriginSelection.regularD (l+1) (z*n) r / (r : ℂ))) ∧
    (∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      ComplexKernelDebye.radialCoefficient n hn z u (1 : Poly) r = 0) := by
  constructor
  · intro p l hp hh
    exact Packet01PoloidalCoefficients.electric_radial_tangential_actual
      n hn z hz u hker p l hp hh
  · exact Packet01Monopole.monopole_radial_coefficient_eq_zero n hn z hz u hker

end OQ14.Packet01CoefficientChain
#check OQ14.Packet01CoefficientChain.actual_electric_coefficients
#print axioms OQ14.Packet01CoefficientChain.actual_electric_coefficients

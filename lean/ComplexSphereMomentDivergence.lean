import HarmonicRadialTestGradient

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexSphereMomentDivergence
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.RadialNormTest OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial
  OQ14.AngularPower OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

theorem harmonic_radial_coupling (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) :
    (∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) *
      ∫ ω : AngularPower.Sphere, response (ModalWeightedMode.coefficient n hn) z 1 u
        (VectorFourier.coordinateMap (r • (ω : Space))) j *
        (deriv η r * (((ω : Space) j : ℝ) : ℂ) * (r : ℂ)^(l+1) * angularPolynomial p ω +
         η r * (r : ℂ)^l * angularPolynomial (pderiv j p) ω) ∂angularMeasure) = 0 := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.ne' rfl
  have h := ComplexSpherePolarDivergence.polar_radial_divergence n hn z hz u hker η hη hc hs p
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  apply congrArg (fun t : ℂ => (r^2 : ℂ) * t)
  apply integral_congr_ae
  filter_upwards with ω
  rw [HarmonicRadialTestGradient.derivative_on_ray η hη h0 p l hp r hr ω j]

#print axioms OQ14.ComplexSphereMomentDivergence.harmonic_radial_coupling
end OQ14.ComplexSphereMomentDivergence

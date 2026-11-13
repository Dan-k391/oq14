import Packet04VectorAngular
import Packet04ToroidalMoments
import ToroidalPlaneWaveMoment

/-! Match the actual componentwise polynomial moments to the complete vector
sphere modes, with the repository's grad(P) cross x toroidal convention. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04AngularDictionary
open Complex MeasureTheory MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.AngularPower OQ14.HarmonicMomentCoupling OQ14.PolynomialVectorCalculus
  OQ14.VectorHarmonicSpan OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

theorem polynomial_mode_pairing (Q : Fin 3 → Poly) (F : Ambient) :
    (∫ ω : Sphere, ⟪embedVector (vectorMap Q ω), F ω⟫ ∂angularMeasure) =
      ∫ ω : Sphere, ∑ j : Fin 3, F ω j * complexEvaluate (Q j) (ω : Space) ∂angularMeasure := by
  apply integral_congr_ae
  filter_upwards with ω
  simp only [PiLp.inner_apply, RCLike.inner_apply, embed_apply, vectorMap_apply,
    SpherePolynomial.polynomialMap_apply, Complex.conj_ofReal, complexEvaluate, evaluate, mul_comm]

theorem radial_pairing (p : Poly) (F : Ambient) :
    (∫ ω : Sphere, ⟪embedVector (vectorMap (radial p) ω), F ω⟫ ∂angularMeasure) =
      ∫ ω : Sphere, ∑ j : Fin 3, F ω j * radialWeight p j ω ∂angularMeasure := by
  rw [polynomial_mode_pairing]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [radial, complexEvaluate, evaluate, eval_mul, eval_X, Complex.ofReal_mul,
    radialWeight, SphericalMomentEquation.angularPolynomial]

theorem poloidal_pairing (p : Poly) (l : ℕ) (F : Ambient) :
    (∫ ω : Sphere, ⟪embedVector (vectorMap (AngularHarmonicEnergy.tangential p l) ω), F ω⟫ ∂angularMeasure) =
      ∫ ω : Sphere, ∑ j : Fin 3, F ω j *
        (gradientWeight p j ω-(l : ℂ)*radialWeight p j ω) ∂angularMeasure := by
  rw [polynomial_mode_pairing]
  apply integral_congr_ae
  filter_upwards with ω
  apply Finset.sum_congr rfl
  intro j _
  simp [AngularHarmonicEnergy.tangential, complexEvaluate, evaluate,
    gradientWeight, radialWeight, SphericalMomentEquation.angularPolynomial]

theorem toroidal_pairing (p : Poly) (F : Ambient) :
    (∫ ω : Sphere, ⟪embedVector (vectorMap (tor (grad p)) ω), F ω⟫ ∂angularMeasure) =
      ∫ ω : Sphere, ∑ j : Fin 3, F ω j *
        DebyeRadialTrace.angularToroidal p (ω : Space) j ∂angularMeasure := by
  rw [polynomial_mode_pairing, tor_grad]
  simp only [ToroidalPlaneWaveMoment.evaluate_toroidal]

theorem actual_moments_separate (F : Ambient)
    (hR : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      (∫ ω : Sphere, ∑ j : Fin 3, F ω j * radialWeight p j ω ∂angularMeasure) = 0)
    (hP : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      (∫ ω : Sphere, ∑ j : Fin 3, F ω j *
        (gradientWeight p j ω-(l : ℂ)*radialWeight p j ω) ∂angularMeasure) = 0)
    (hT : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      (∫ ω : Sphere, ∑ j : Fin 3, F ω j *
        DebyeRadialTrace.angularToroidal p (ω : Space) j ∂angularMeasure) = 0) : F = 0 := by
  apply Packet04VectorAngular.polynomial_integral_moments_separate F
  · intro a
    exact (radial_pairing (SphereHarmonicBasis.representative a.1 a.2) F).trans
      (hR _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2))
  · intro a
    exact (poloidal_pairing (SphereHarmonicBasis.representative a.1 a.2) a.1 F).trans
      (hP _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2))
  · intro a
    exact (toroidal_pairing (SphereHarmonicBasis.representative a.1 a.2) F).trans
      (hT _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2))

end OQ14.Packet04AngularDictionary
#print axioms OQ14.Packet04AngularDictionary.polynomial_mode_pairing
#print axioms OQ14.Packet04AngularDictionary.radial_pairing
#print axioms OQ14.Packet04AngularDictionary.poloidal_pairing
#print axioms OQ14.Packet04AngularDictionary.toroidal_pairing
#print axioms OQ14.Packet04AngularDictionary.actual_moments_separate

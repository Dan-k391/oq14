import Packet04AngularDictionary

/-! Linear polynomial coordinates for vector spherical harmonics, and the
finite three-coordinate reduction of the degree-one sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04PolynomialCoordinates
open Complex MeasureTheory MvPolynomial OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolynomialVectorCalculus OQ14.VectorHarmonicSpan
  OQ14.VectorHarmonicBasisSpan OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

theorem degree_zero (p : Poly) (hp : p.IsHomogeneous 0) : p = p.coeff 0 • (1 : Poly) := by
  rw [smul_eq_C_mul, mul_one]
  exact totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hp)

theorem degree_one (p : Poly) (hp : p.IsHomogeneous 1) :
    p = ∑ i : Fin 3, (pderiv i p).coeff 0 • (X i : Poly) := by
  have he := hp.sum_X_mul_pderiv
  simp only [one_nsmul] at he
  conv_lhs => rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  have hd : (pderiv i p).IsHomogeneous 0 := by simpa using hp.pderiv (i := i)
  have hc := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hd)
  calc
    X i * pderiv i p = X i * C ((pderiv i p).coeff 0) := congrArg (fun q => X i*q) hc
    _ = (pderiv i p).coeff 0 • (X i : Poly) := by rw [smul_eq_C_mul, mul_comm]

def vectorCoordinate (F : Ambient) : Vec →ₗ[ℝ] ℂ where
  toFun Q := ⟪realLift (VectorHarmonicSeparation.lift (vectorMap Q)), F⟫
  map_add' Q V := by simp [VectorHarmonicSeparation.lift, map_add, inner_add_left]
  map_smul' c Q := by
    simp only [VectorHarmonicSeparation.lift, map_smul]
    simp only [← algebraMap_smul ℂ c, RCLike.algebraMap_eq_ofReal, inner_smul_real_left]
    rfl

def radialCoordinate (F : Ambient) : Poly →ₗ[ℝ] ℂ :=
  (vectorCoordinate F).comp radialLinear

def poloidalLinear (l : ℕ) : Poly →ₗ[ℝ] Vec := gradLinear - (l : ℝ) • radialLinear

theorem poloidalLinear_apply (p : Poly) (l : ℕ) :
    poloidalLinear l p = AngularHarmonicEnergy.tangential p l := by
  funext i
  rfl

def poloidalCoordinate (F : Ambient) (l : ℕ) : Poly →ₗ[ℝ] ℂ :=
  (vectorCoordinate F).comp (poloidalLinear l)

def toroidalCoordinate (F : Ambient) : Poly →ₗ[ℝ] ℂ :=
  (vectorCoordinate F).comp (torLinear.comp gradLinear)

theorem radial_actual (F : Ambient) (p : Poly) : radialCoordinate F p =
    ∫ ω : Sphere, ∑ j : Fin 3, F ω j * HarmonicMomentCoupling.radialWeight p j ω
      ∂angularMeasure := by
  change ⟪realLift (VectorHarmonicSeparation.lift (vectorMap (radial p))), F⟫ = _
  rw [Packet04VectorAngular.continuous_mode_coefficient_integral]
  exact Packet04AngularDictionary.radial_pairing p F

theorem poloidal_actual (F : Ambient) (p : Poly) (l : ℕ) : poloidalCoordinate F l p =
    ∫ ω : Sphere, ∑ j : Fin 3, F ω j *
      (HarmonicMomentCoupling.gradientWeight p j ω -
        (l : ℂ) * HarmonicMomentCoupling.radialWeight p j ω) ∂angularMeasure := by
  change vectorCoordinate F (poloidalLinear l p) = _
  rw [poloidalLinear_apply]
  change ⟪realLift (VectorHarmonicSeparation.lift
    (vectorMap (AngularHarmonicEnergy.tangential p l))), F⟫ = _
  rw [Packet04VectorAngular.continuous_mode_coefficient_integral]
  exact Packet04AngularDictionary.poloidal_pairing p l F

theorem toroidal_actual (F : Ambient) (p : Poly) : toroidalCoordinate F p =
    ∫ ω : Sphere, ∑ j : Fin 3, F ω j *
      DebyeRadialTrace.angularToroidal p (ω : Space) j ∂angularMeasure := by
  change ⟪realLift (VectorHarmonicSeparation.lift (vectorMap (tor (grad p)))), F⟫ = _
  rw [Packet04VectorAngular.continuous_mode_coefficient_integral]
  exact Packet04AngularDictionary.toroidal_pairing p F

theorem degree_one_coordinate (L : Poly →ₗ[ℝ] ℂ) (p : Poly) (hp : p.IsHomogeneous 1) :
    L p = ∑ i : Fin 3, (pderiv i p).coeff 0 • L (X i) := by
  conv_lhs => rw [degree_one p hp]
  simp only [map_sum, map_smul]

theorem separate_with_dipole_coordinates (F : Ambient)
    (hR : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      l ≠ 1 → radialCoordinate F p = 0)
    (hP : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      l ≠ 1 → poloidalCoordinate F l p = 0)
    (hRx : ∀ i : Fin 3, radialCoordinate F (X i) = 0)
    (hPx : ∀ i : Fin 3, poloidalCoordinate F 1 (X i) = 0)
    (hT : ∀ (p : Poly) (l : ℕ), p.IsHomogeneous l → formalLaplacian p = 0 →
      toroidalCoordinate F p = 0) : F = 0 := by
  apply Packet04VectorAngular.polynomial_moments_separate F
  · intro a
    change radialCoordinate F (SphereHarmonicBasis.representative a.1 a.2) = 0
    by_cases h1 : a.1 = 1
    · rw [degree_one_coordinate _ _ (h1 ▸ SphereHarmonicBasis.representative_homogeneous a.1 a.2)]
      simp only [hRx, smul_zero, Finset.sum_const_zero]
    · exact hR _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2) h1
  · intro a
    change vectorCoordinate F (AngularHarmonicEnergy.tangential
      (SphereHarmonicBasis.representative a.1 a.2) a.1) = 0
    rw [← poloidalLinear_apply]
    change poloidalCoordinate F a.1 (SphereHarmonicBasis.representative a.1 a.2) = 0
    by_cases h1 : a.1 = 1
    · have he : poloidalCoordinate F a.1 = poloidalCoordinate F 1 := congrArg (poloidalCoordinate F) h1
      rw [he, degree_one_coordinate _ _ (h1 ▸ SphereHarmonicBasis.representative_homogeneous a.1 a.2)]
      simp only [hPx, smul_zero, Finset.sum_const_zero]
    · exact hP _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
        (SphereHarmonicBasis.representative_harmonic a.1 a.2) h1
  · intro a
    exact hT _ _ (SphereHarmonicBasis.representative_homogeneous a.1 a.2)
      (SphereHarmonicBasis.representative_harmonic a.1 a.2)

end OQ14.Packet04PolynomialCoordinates
#print axioms OQ14.Packet04PolynomialCoordinates.degree_zero
#print axioms OQ14.Packet04PolynomialCoordinates.degree_one
#print axioms OQ14.Packet04PolynomialCoordinates.poloidalLinear_apply
#print axioms OQ14.Packet04PolynomialCoordinates.radial_actual
#print axioms OQ14.Packet04PolynomialCoordinates.poloidal_actual
#print axioms OQ14.Packet04PolynomialCoordinates.toroidal_actual
#print axioms OQ14.Packet04PolynomialCoordinates.degree_one_coordinate
#print axioms OQ14.Packet04PolynomialCoordinates.separate_with_dipole_coordinates

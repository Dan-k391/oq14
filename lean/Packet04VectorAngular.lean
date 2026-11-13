import ModalVectorAngularSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet04VectorAngular
open MeasureTheory OQ14.ModalVectorAngularSlices OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

/-- The established scalar and transverse harmonic coordinates determine an
angular vector field in L². The transverse coordinates are those of its
orthogonal tangential part. -/
theorem eq_of_radial_transverse_coefficients (F G : Ambient)
    (hr : ∀ a : SphereHarmonicHilbert.TotalIndex,
      ⟪ComplexHarmonicBasis.vector a, radial F⟫ =
        ⟪ComplexHarmonicBasis.vector a, radial G⟫)
    (ht : ∀ a : ComplexTransverseExpansion.ModeIndex,
      ⟪ComplexTransverseExpansion.vector a, tangent F⟫ =
        ⟪ComplexTransverseExpansion.vector a, tangent G⟫) : F = G := by
  have hrad : radial F = radial G := by
    apply HasSum.unique (ComplexHarmonicBasis.expansion (radial F))
    convert ComplexHarmonicBasis.expansion (radial G) using 1
    funext a
    rw [hr a]
  have htan : tangent F = tangent G := by
    apply HasSum.unique (ComplexTransverseExpansion.expansion (tangent F) (tangent_isTangential F))
    convert ComplexTransverseExpansion.expansion (tangent G) (tangent_isTangential G) using 1
    funext a
    rw [ht a]
  apply Lp.ext
  filter_upwards [vector_decomposition_ae F, vector_decomposition_ae G] with n hf hg
  rw [hrad, htan] at hf
  exact hf.trans hg.symm

/-- A radial harmonic coordinate is the corresponding actual sphere integral. -/
theorem radial_coefficient_integral (F : Ambient)
    (a : SphereHarmonicHilbert.TotalIndex) :
    ⟪ComplexHarmonicBasis.vector a, radial F⟫ =
      ∫ n : SphereHarmonicBasis.Sphere,
        (SphereHarmonicBasis.angular a.1 a.2 n : ℂ) *
          ⟪embedVector (n : Maxwell.Space), F n⟫ ∂SphereHarmonicBasis.angularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radial_actual F,
    (ComplexHarmonicBasis.complexAngular a).coeFn_toLp (p := 2) (𝕜 := ℂ)
      SphereHarmonicBasis.angularMeasure] with n hn ha
  rw [ComplexHarmonicBasis.vector_toLp] at *
  rw [ha, hn]
  simp [ComplexHarmonicBasis.complexAngular, radialFunction, RCLike.inner_apply, mul_comm]

/-- Complexification of any real vector spherical-harmonic moment. -/
theorem real_mode_coefficient (v : RealAmbient) (F : Ambient) :
    ⟪realLift v, F⟫ =
      ((@inner ℝ _ _ v (realPart F) : ℝ) : ℂ) +
      Complex.I * ((@inner ℝ _ _ v (imagPart F) : ℝ) : ℂ) := by
  conv_lhs => rw [real_imag_decomposition F]
  rw [inner_add_right, inner_smul_right, realLift_inner, realLift_inner]

/-- The genuine radial, poloidal and toroidal polynomial harmonic modes
separate complex vector fields on the sphere. -/
theorem polynomial_moments_separate (F : Ambient)
    (hR : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.radialField a)), F⟫ = 0)
    (hP : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.poloidalField a)), F⟫ = 0)
    (hT : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.toroidalField a)), F⟫ = 0) : F = 0 := by
  have hre (v : RealAmbient) (h : ⟪realLift v, F⟫ = 0) :
      @inner ℝ _ _ (realPart F) v = 0 := by
    rw [real_mode_coefficient] at h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, zero_mul,
      mul_zero, sub_zero, add_zero] at hh
    rw [real_inner_comm]
    exact hh
  have him (v : RealAmbient) (h : ⟪realLift v, F⟫ = 0) :
      @inner ℝ _ _ (imagPart F) v = 0 := by
    rw [real_mode_coefficient] at h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, zero_mul,
      mul_zero, one_mul, zero_add, add_zero] at hh
    rw [real_inner_comm]
    exact hh
  have hr : realPart F = 0 :=
    VectorHarmonicSeparation.moments_separate _ (fun a => hre _ (hR a))
      (fun a => hre _ (hP a)) (fun a => hre _ (hT a))
  have hi : imagPart F = 0 :=
    VectorHarmonicSeparation.moments_separate _ (fun a => him _ (hR a))
      (fun a => him _ (hP a)) (fun a => him _ (hT a))
  rw [real_imag_decomposition F, hr, hi]
  simp

/-- The Hilbert-space coefficient against a continuous real vector mode is
its actual complex bilinear sphere moment. -/
theorem continuous_mode_coefficient_integral
    (m : C(SphereHarmonicBasis.Sphere, Maxwell.Space)) (F : Ambient) :
    ⟪realLift (VectorHarmonicSeparation.lift m), F⟫ =
      ∫ n : SphereHarmonicBasis.Sphere, ⟪embedVector (m n), F n⟫
        ∂SphereHarmonicBasis.angularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [embedVector.coeFn_compLpL (VectorHarmonicSeparation.lift m),
    m.coeFn_toLp (p := 2) (𝕜 := ℝ) SphereHarmonicBasis.angularMeasure] with n h1 h2
  change realLift (VectorHarmonicSeparation.lift m) n =
    embedVector (VectorHarmonicSeparation.lift m n) at h1
  rw [h1, h2]

/-- Vanishing of all actual polynomial radial, surface-gradient, and
cross-gradient moments forces the sphere field to vanish in L². -/
theorem polynomial_integral_moments_separate (F : Ambient)
    (hR : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.radialField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = 0)
    (hP : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.poloidalField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = 0)
    (hT : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.toroidalField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = 0) : F = 0 := by
  apply polynomial_moments_separate F
  · intro a
    rw [continuous_mode_coefficient_integral]
    exact hR a
  · intro a
    rw [continuous_mode_coefficient_integral]
    exact hP a
  · intro a
    rw [continuous_mode_coefficient_integral]
    exact hT a

/-- Equality of all genuine polynomial vector-mode coordinates determines
an arbitrary complex sphere field. -/
theorem eq_of_polynomial_moments (F G : Ambient)
    (hR : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.radialField a)), F⟫ =
      ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.radialField a)), G⟫)
    (hP : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.poloidalField a)), F⟫ =
      ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.poloidalField a)), G⟫)
    (hT : ∀ a, ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.toroidalField a)), F⟫ =
      ⟪realLift (VectorHarmonicSeparation.lift
      (VectorHarmonicBasisSpan.toroidalField a)), G⟫) : F = G := by
  apply sub_eq_zero.mp
  apply polynomial_moments_separate (F - G)
  · intro a
    rw [inner_sub_right, hR a, sub_self]
  · intro a
    rw [inner_sub_right, hP a, sub_self]
  · intro a
    rw [inner_sub_right, hT a, sub_self]

/-- Equality of all physical polynomial vector moments determines the
complex angular field. -/
theorem eq_of_polynomial_integral_moments (F G : Ambient)
    (hR : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.radialField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.radialField a n), G n⟫
      ∂SphereHarmonicBasis.angularMeasure))
    (hP : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.poloidalField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.poloidalField a n), G n⟫
      ∂SphereHarmonicBasis.angularMeasure))
    (hT : ∀ a, (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.toroidalField a n), F n⟫
      ∂SphereHarmonicBasis.angularMeasure) = (∫ n : SphereHarmonicBasis.Sphere,
      ⟪embedVector (VectorHarmonicBasisSpan.toroidalField a n), G n⟫
      ∂SphereHarmonicBasis.angularMeasure)) : F = G := by
  apply eq_of_polynomial_moments F G
  · intro a
    simpa only [continuous_mode_coefficient_integral] using hR a
  · intro a
    simpa only [continuous_mode_coefficient_integral] using hP a
  · intro a
    simpa only [continuous_mode_coefficient_integral] using hT a

#print axioms OQ14.Packet04VectorAngular.eq_of_polynomial_integral_moments

#print axioms OQ14.Packet04VectorAngular.eq_of_polynomial_moments

#print axioms OQ14.Packet04VectorAngular.continuous_mode_coefficient_integral
#print axioms OQ14.Packet04VectorAngular.polynomial_integral_moments_separate

#print axioms OQ14.Packet04VectorAngular.real_mode_coefficient
#print axioms OQ14.Packet04VectorAngular.polynomial_moments_separate

#print axioms OQ14.Packet04VectorAngular.radial_coefficient_integral

#print axioms OQ14.Packet04VectorAngular.eq_of_radial_transverse_coefficients
end OQ14.Packet04VectorAngular

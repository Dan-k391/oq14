import PolarIntegration

/-! # Actual polar integration with complex or Banach-valued integrands

The genuine Euclidean polar measure identity is reused without changing the
frozen real-valued module. Both Fubini and the radial Jacobian hold for Bochner
integrals, including integrability of the resulting radial moment.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.ComplexPolarIntegration

open MeasureTheory Metric OQ14.Maxwell OQ14.AngularPower OQ14.PolarIntegration
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_polar_product (f : Space → E) :
    (∫ x, f x) =
      ∫ p : Sphere × Radius, f ((p.2 : ℝ) • (p.1 : Space))
        ∂angularMeasure.prod radialMeasure := by
  calc
    _ = ∫ x : Punctured, f x ∂(volume.comap ((↑) : Punctured → Space)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = _ := by
      have h := polar_measurePreserving.integral_comp
        (homeomorphUnitSphereProd Space).measurableEmbedding
        (fun p : Sphere × Radius => f ((homeomorphUnitSphereProd Space).symm p))
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using h

omit [NormedSpace ℝ E] in
theorem integrable_polar_product (f : Space → E) (hf : Integrable f) :
    Integrable (fun p : Sphere × Radius => f ((p.2 : ℝ) • (p.1 : Space)))
      (angularMeasure.prod radialMeasure) := by
  have hi : Integrable (fun x : Punctured => f x)
      ((volume : Measure Space).comap ((↑) : Punctured → Space)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have h := polar_measurePreserving.integrable_comp_emb
    (homeomorphUnitSphereProd Space).measurableEmbedding
    (g := fun p : Sphere × Radius => f ((homeomorphUnitSphereProd Space).symm p))
  apply h.mp
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hi

theorem integral_radialMeasure (g : Radius → E) :
    (∫ r, g r ∂radialMeasure) =
      ∫ r : Radius, (r : ℝ)^2 • g r ∂((volume : Measure ℝ).comap ((↑) : Radius → ℝ)) := by
  simp only [radialMeasure, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · apply integral_congr_ae
    filter_upwards with r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem integrable_radialMeasure_iff (g : Radius → E) :
    Integrable g radialMeasure ↔
      Integrable (fun r : Radius => (r : ℝ)^2 • g r)
        ((volume : Measure ℝ).comap ((↑) : Radius → ℝ)) := by
  simp only [radialMeasure, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integrable_withDensity_iff_integrable_smul
    (measurable_subtype_coe.pow_const _).real_toNNReal]
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _)]

theorem integral_polar (f : Space → E) (hf : Integrable f) :
    (∫ x, f x) =
      ∫ r in Set.Ioi (0 : ℝ), r^2 •
        (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure) := by
  rw [integral_polar_product, integral_prod_symm _ (integrable_polar_product f hf),
    integral_radialMeasure]
  exact integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => r^2 • ∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure)

theorem integrable_radial_moment (f : Space → E) (hf : Integrable f) :
    IntegrableOn (fun r : ℝ => r^2 •
      (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure)) (Set.Ioi 0) := by
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mpr
  exact (integrable_radialMeasure_iff _).mp
    (integrable_polar_product f hf).integral_prod_right

theorem integral_polar_complex (f : Space → ℂ) (hf : Integrable f) :
    (∫ x, f x) =
      ∫ r in Set.Ioi (0 : ℝ), (r^2 : ℂ) *
        (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure) := by
  simpa only [Complex.real_smul, Complex.ofReal_pow] using integral_polar f hf

theorem integrable_radial_moment_complex (f : Space → ℂ) (hf : Integrable f) :
    IntegrableOn (fun r : ℝ => (r^2 : ℂ) *
      (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure)) (Set.Ioi 0) := by
  simpa only [Complex.real_smul, Complex.ofReal_pow] using integrable_radial_moment f hf

end OQ14.ComplexPolarIntegration

#print axioms OQ14.ComplexPolarIntegration.integral_polar_product
#print axioms OQ14.ComplexPolarIntegration.integrable_polar_product
#print axioms OQ14.ComplexPolarIntegration.integral_radialMeasure
#print axioms OQ14.ComplexPolarIntegration.integrable_radialMeasure_iff
#print axioms OQ14.ComplexPolarIntegration.integral_polar
#print axioms OQ14.ComplexPolarIntegration.integrable_radial_moment
#print axioms OQ14.ComplexPolarIntegration.integral_polar_complex
#print axioms OQ14.ComplexPolarIntegration.integrable_radial_moment_complex

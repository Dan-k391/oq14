import AngularPower

/-! # Actual Euclidean polar integration for outgoing power -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.PolarIntegration

open MeasureTheory Metric OQ14.Maxwell OQ14.AngularPower
open scoped ENNReal

abbrev Radius := Set.Ioi (0 : ℝ)
abbrev Punctured := ({(0 : Space)}ᶜ : Set Space)

def radialMeasure : Measure Radius := Measure.volumeIoiPow 2

instance : SigmaFinite radialMeasure := inferInstanceAs (SigmaFinite (Measure.volumeIoiPow 2))

theorem polar_measurePreserving :
    MeasurePreserving (homeomorphUnitSphereProd Space)
      ((volume : Measure Space).comap ((↑) : Punctured → Space))
      (angularMeasure.prod radialMeasure) := by
  simpa only [angularMeasure, radialMeasure, finrank_euclideanSpace,
    Fintype.card_fin, Nat.reduceSub] using
      (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd

theorem integral_polar_product (f : Space → ℝ) :
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

theorem integrable_polar_product (f : Space → ℝ) (hf : Integrable f) :
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

theorem integral_radialMeasure (g : Radius → ℝ) :
    (∫ r, g r ∂radialMeasure) =
      ∫ r : Radius, (r : ℝ)^2 * g r ∂((volume : Measure ℝ).comap ((↑) : Radius → ℝ)) := by
  simp only [radialMeasure, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · apply integral_congr_ae
    filter_upwards with r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem integral_polar (f : Space → ℝ) (hf : Integrable f) :
    (∫ x, f x) =
      ∫ r in Set.Ioi (0 : ℝ), r^2 *
        (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure) := by
  rw [integral_polar_product, integral_prod_symm _ (integrable_polar_product f hf),
    integral_radialMeasure]
  exact integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => r^2 * ∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure)

end OQ14.PolarIntegration

#print axioms OQ14.PolarIntegration.polar_measurePreserving
#print axioms OQ14.PolarIntegration.integral_polar_product
#print axioms OQ14.PolarIntegration.integrable_polar_product
#print axioms OQ14.PolarIntegration.integral_radialMeasure
#print axioms OQ14.PolarIntegration.integral_polar

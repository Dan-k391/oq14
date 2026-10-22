import ConicalRadialTests

/-! Actual product integrability and radial/angular Fubini for compact conical test pairings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalPolarTests
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
open scoped Topology

theorem test_product_integrable (R : ℝ) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioo (0 : ℝ) R)) (H : Sphere → ℝ) (hH : Integrable H angularMeasure)
    (ψ : Space → ℝ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × Sphere => f p.1*H p.2*ψ (p.1 • (p.2 : Space)))
      ((volume.restrict (Ioo (0 : ℝ) R)).prod angularMeasure) := by
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuous hψ
  have hc : Continuous (fun p : ℝ × Sphere => ψ (p.1 • (p.2 : Space))) :=
    hψ.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  apply ((hf.norm.mul_prod hH.norm).const_mul |C|).mono'
    ((hf.aestronglyMeasurable.fst.mul hH.aestronglyMeasurable.snd).mul hc.aestronglyMeasurable)
  filter_upwards with p
  change ‖f p.1*H p.2*ψ (p.1 • (p.2 : Space))‖ ≤ |C| * (‖f p.1‖*‖H p.2‖)
  simp only [norm_mul]
  calc
    ‖f p.1‖*‖H p.2‖*‖ψ (p.1 • (p.2 : Space))‖ ≤ ‖f p.1‖*‖H p.2‖*|C| :=
      mul_le_mul_of_nonneg_left ((hC _).trans (le_abs_self C)) (by positivity)
    _ = |C| * (‖f p.1‖*‖H p.2‖) := by ring

theorem power_test_integrable (β R : ℝ) (hβ : -1 < β) (hR : 0 < R)
    (H : Sphere → ℝ) (hH : Integrable H angularMeasure)
    (ψ : Space → ℝ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × Sphere => p.1^β*H p.2*ψ (p.1 • (p.2 : Space)))
      ((volume.restrict (Ioo (0 : ℝ) R)).prod angularMeasure) := by
  apply test_product_integrable R (fun r : ℝ => r^β) _ H hH ψ hψ hcompact
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mp
    (intervalIntegral.intervalIntegrable_rpow' hβ)

theorem power_test_swap (β R : ℝ) (hβ : -1 < β) (hR : 0 < R)
    (H : Sphere → ℝ) (hH : Integrable H angularMeasure)
    (ψ : Space → ℝ) (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^β*H n*ψ (r • (n : Space)) ∂angularMeasure) =
    ∫ n : Sphere, (∫ r in Ioo (0 : ℝ) R, r^β*H n*ψ (r • (n : Space))) ∂angularMeasure := by
  exact integral_integral_swap (power_test_integrable β R hβ hR H hH ψ hψ hcompact)

end OQ14.ConicalPolarTests

#print axioms OQ14.ConicalPolarTests.test_product_integrable
#print axioms OQ14.ConicalPolarTests.power_test_integrable
#print axioms OQ14.ConicalPolarTests.power_test_swap

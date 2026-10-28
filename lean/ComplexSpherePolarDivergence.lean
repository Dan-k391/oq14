import ComplexSphereDivergence

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexSpherePolarDivergence
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ExteriorHelmholtz OQ14.RadialNormTest
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.AngularPower OQ14.ComplexSphereDivergence
open scoped Topology

theorem polar_radial_divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1) (p : Poly) :
    (∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) *
      ∫ ω : Sphere, response (ModalWeightedMode.coefficient n hn) z 1 u
        (VectorFourier.coordinateMap (r • (ω : Space))) j *
        dcoord (test η p) (r • (ω : Space)) j ∂angularMeasure) = 0 := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.ne' rfl
  have ht := test_regular η hη h0 p
  have htc := test_compact η hc p
  have hsupport : tsupport (test η p) ⊆ ball (0 : Space) 1 := by
    intro x hx
    have h := hs (radialNorm_tsupport η (tsupport_mul_subset_left hx))
    simpa only [mem_ball, dist_zero_right] using h.2
  have h := actual_divergence n hn z hz u hker (test η p) ht htc hsupport
  have hi (j : Fin 3) : Integrable (fun x : Space => response (ModalWeightedMode.coefficient n hn) z 1 u
      (VectorFourier.coordinateMap x) j * dcoord (test η p) x j) := by
    apply PointSingularity.test_product_integrable _ _
      (ComplexSphereHelmholtz.actual_locallyIntegrable n hn z u j)
    · exact partial_continuous (ht.of_le (by simp)) j
    · exact htc.fderiv_apply ℝ (basis j)
  simpa only [← ComplexPolarIntegration.integral_polar_complex _ (hi _)] using h

#print axioms OQ14.ComplexSpherePolarDivergence.polar_radial_divergence
end OQ14.ComplexSpherePolarDivergence

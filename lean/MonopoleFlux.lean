import HarmonicMomentIntegrability
import ComplexKernelDebye

/-! Actual weak radial flux conservation for the degree-zero electric coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.MonopoleFlux
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
  OQ14.ComplexKernelResponse OQ14.ExteriorHelmholtz OQ14.RadialNormTest
open scoped Topology

theorem constant_test_derivative (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (r : ℝ) (hr : 0 < r) (ω : Sphere) (j : Fin 3) :
    dcoord (test η (1 : Poly)) (r • (ω : Space)) j =
      deriv η r * (((ω : Space) j : ℝ) : ℂ) := by
  have he : test η (1 : Poly) = radialNorm η := by
    funext x
    simp [test, complexEvaluate, evaluate]
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr]
  have hx : r • (ω : Space) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact hr.ne')
  rw [he, radialNorm_partial η hη _ hx j, hnorm]
  simp [GreenKernel.unitCoordinate, hnorm, PiLp.smul_apply, Complex.ofReal_mul, hr.ne']

theorem actual_weak_flux (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^2 * deriv η r *
      radialMoment (ComplexKernelDebye.coordinates n hn z u) (1 : Poly) r) = 0 := by
  let E := response (ModalWeightedMode.coefficient n hn) z 1 u
  have h := ComplexSpherePolarDivergence.polar_radial_divergence n hn z hz u hker η hη hc hs (1 : Poly)
  have he (j : Fin 3) :
      (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere, E (VectorFourier.coordinateMap (r • (ω : Space))) j *
        dcoord (test η (1 : Poly)) (r • (ω : Space)) j ∂angularMeasure) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^2 * deriv η r *
        moment (NewtonL2.physicalCoordinate E j) (radialWeight (1 : Poly) j) r := by
    apply integral_congr_ae
    filter_upwards [PolarMomentAE.polar_ae (NewtonL2.physicalCoordinate_ae E j),
      ae_restrict_mem measurableSet_Ioi] with r hr hri
    have hang : (∫ ω : Sphere, E (VectorFourier.coordinateMap (r • (ω : Space))) j *
        dcoord (test η (1 : Poly)) (r • (ω : Space)) j ∂angularMeasure) =
        deriv η r * moment (NewtonL2.physicalCoordinate E j) (radialWeight (1 : Poly) j) r := by
      rw [moment, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hr] with ω hω
      rw [constant_test_derivative η hη r hri ω j, hω]
      simp only [radialWeight, angularPolynomial, complexEvaluate, evaluate, map_one, Complex.ofReal_one, mul_one]
      ring
    rw [hang]
    ring
  change (∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : Sphere, E (VectorFourier.coordinateMap (r • (ω : Space))) j *
    dcoord (test η (1 : Poly)) (r • (ω : Space)) j ∂angularMeasure) = 0 at h
  simp_rw [he] at h
  have hi (j : Fin 3) : IntegrableOn (fun r : ℝ => (r : ℂ)^2 * deriv η r *
      moment (NewtonL2.physicalCoordinate E j) (radialWeight (1 : Poly) j) r) (Ioi 0) :=
    radial_integrable _ _ (radial_weight_continuous _ _) (weight_memLp _ _).1
      (deriv η) (contDiff_infty_iff_deriv.mp hη).2 hc.deriv 1
  have heq : (fun r : ℝ => (r : ℂ)^2 * deriv η r *
      radialMoment (ComplexKernelDebye.coordinates n hn z u) (1 : Poly) r) =
      fun r : ℝ => ∑ j : Fin 3, (r : ℂ)^2 * deriv η r *
        moment (NewtonL2.physicalCoordinate E j) (radialWeight (1 : Poly) j) r := by
    funext r
    simp only [radialMoment, Finset.mul_sum, ComplexKernelDebye.coordinates, E]
  rw [heq, integral_finset_sum _ (fun j _ => hi j)]
  exact h

end OQ14.MonopoleFlux
#print axioms OQ14.MonopoleFlux.constant_test_derivative
#print axioms OQ14.MonopoleFlux.actual_weak_flux

import ComplexSpherePolarDivergence

noncomputable section
set_option autoImplicit false
namespace OQ14.HarmonicRadialTestGradient
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.RadialNormTest OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial
  OQ14.FischerDecomposition OQ14.AngularPower MvPolynomial
open scoped Topology

theorem derivative_on_ray (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (h0 : 0 ∉ tsupport η) (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (r : ℝ) (hr : 0 < r) (ω : AngularPower.Sphere) (j : Fin 3) :
    dcoord (test η p) (r • (ω : Space)) j =
      deriv η r * (((ω : Space) j : ℝ) : ℂ) * (r : ℂ)^(l+1) * angularPolynomial p ω +
      η r * (r : ℂ)^l * angularPolynomial (pderiv j p) ω := by
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr]
  have hx : r • (ω : Space) ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact hr.ne')
  have hreg := (radialNorm_smooth η hη h0).differentiable (by simp) (r • (ω : Space))
  have hpreg := (complexEvaluate_regular p).differentiable (by simp) (r • (ω : Space))
  have hpd : (pderiv j p).IsHomogeneous l := by simpa using hp.pderiv (i := j)
  rw [show test η p = fun y => radialNorm η y * complexEvaluate p y from rfl,
    partial_mul hreg hpreg, radialNorm_partial η hη _ hx j, complexEvaluate_partial,
    complexEvaluate_smul p (l+1) hp, hnorm]
  change radialNorm η (r • (ω : Space)) * complexEvaluate (pderiv j p) (r • (ω : Space)) + _ = _
  rw [complexEvaluate_smul (pderiv j p) l hpd]
  have hu : GreenKernel.unitCoordinate j (r • (ω : Space)) = (((ω : Space) j : ℝ) : ℂ) := by
    simp [GreenKernel.unitCoordinate, hnorm, PiLp.smul_apply, Complex.ofReal_mul, hr.ne']
  rw [hu]
  dsimp [radialNorm, angularPolynomial]
  rw [hnorm]
  ring

#print axioms OQ14.HarmonicRadialTestGradient.derivative_on_ray
end OQ14.HarmonicRadialTestGradient

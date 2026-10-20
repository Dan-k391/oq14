import SphericalMomentEquation
import RadialMomentClassical
import RadialMomentODE
import HarmonicMomentSeparation

/-! # Exterior scalar Rellich uniqueness from the actual spatial equation -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarExteriorRellich

open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.AngularPower OQ14.RadialMoment OQ14.RadialMomentClassical
  OQ14.SphericalMomentEquation
open scoped Topology

theorem actual_moment_equation (R : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (heq : ∀ x, R < ‖x‖ → laplacian u x + k^2*u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ r, R < r →
      HasDerivAt (radialFlux (momentD u (angularPolynomial p)))
        (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*moment u (angularPolynomial p) r) r ∧
      momentD u (angularPolynomial p) r =
        radialFlux (momentD u (angularPolynomial p)) r/(r : ℂ)^2 := by
  have h := moment_classical_of_weak l k R hR u hu (angularPolynomial p)
    (angularPolynomial_continuous p) (fun η hη hc hs =>
      weak_radial_real_test R hR k u hu heq p l hp hh η hη hc hs)
  exact fun r hr => (h r hr).2

theorem harmonic_moment_zero (R : ℝ) (hR : 0 ≤ R) (k : ℝ) (hk : 0 < k)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (heq : ∀ x, R < ‖x‖ → laplacian u x + (k : ℂ)^2*u x = 0)
    (hmass : Tendsto (sphericalMass u) atTop (𝓝 0))
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ r, R < r → moment u (angularPolynomial p) r = 0 := by
  have h := actual_moment_equation R hR k u hu heq p l hp hh
  exact RadialMomentODE.moment_zero_of_flux l k hk R hR u hu (angularPolynomial p)
    (angularPolynomial_continuous p) (radialFlux (momentD u (angularPolynomial p)))
    (fun r hr => (h r hr).2) (fun r hr => (h r hr).1) hmass

theorem zero_of_surface_mass (R : ℝ) (hR : 0 ≤ R) (k : ℝ) (hk : 0 < k)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (heq : ∀ x, R < ‖x‖ → laplacian u x + (k : ℂ)^2*u x = 0)
    (hmass : Tendsto (sphericalMass u) atTop (𝓝 0)) :
    ∀ x, R < ‖x‖ → u x = 0 := by
  have hz (r : ℝ) (hr : R < r) : ∀ n : Sphere, u (r • (n : Space)) = 0 := by
    apply HarmonicMomentSeparation.zero_of_harmonic_moments _
      (ray_continuous R r hR hr u hu.continuousOn)
    intro l p hp hh
    have h := harmonic_moment_zero R hR k hk u hu heq hmass p l hp hh r hr
    simpa only [moment, angularPolynomial, HarmonicPolynomial.complexEvaluate,
      HarmonicPolynomial.evaluate, SpherePolynomial.polynomialMap_apply] using h
  intro x hx
  have hpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
  have hn : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (ne_of_gt hpos)]
  let n : Sphere := ⟨‖x‖⁻¹ • x, by simpa only [mem_sphere, dist_zero_right] using hn⟩
  have he : ‖x‖ • (n : Space) = x := by
    dsimp [n]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  simpa only [he] using hz ‖x‖ hx n

end OQ14.ScalarExteriorRellich

#print axioms OQ14.ScalarExteriorRellich.actual_moment_equation
#print axioms OQ14.ScalarExteriorRellich.harmonic_moment_zero
#print axioms OQ14.ScalarExteriorRellich.zero_of_surface_mass

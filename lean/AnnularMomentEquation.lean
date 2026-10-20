import SphericalMomentEquation
import AnnularMoment

/-! # Actual weak spherical moment equations on finite annuli -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.AnnularMomentEquation

open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.RadialNormTest OQ14.HarmonicPolynomial
  OQ14.SphericalMomentEquation OQ14.RadialMoment
open scoped Topology

theorem weak_radial_equation (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (AnnularMoment.annulus R L))
    (heq : ∀ x, x ∈ AnnularMoment.annulus R L → laplacian u x + k^2*u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo R L) :
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * moment u (angularPolynomial p) r *
      radialExpression l k η r) = 0 := by
  have h0 : 0 ∉ tsupport η := fun h => (not_lt_of_ge hR) (hs h).1
  have hφ := test_regular η hη h0 p
  have hφc := test_compact η hc p
  have hφs : tsupport (test η p) ⊆ AnnularMoment.annulus R L := by
    intro x hx
    exact hs (RadialNormTest.radialNorm_tsupport η (tsupport_mul_subset_left hx))
  have hΩ := AnnularMoment.annulus_open R L
  have hur : ∀ x ∈ AnnularMoment.annulus R L, ContDiffAt ℝ (⊤ : ℕ∞) u x :=
    fun x hx => hu.contDiffAt (hΩ.mem_nhds hx)
  obtain ⟨hI, hJ⟩ := local_test_integrable hΩ u (test η p) hur hφ hφc hφs
  have hi : Integrable (fun x => u x*(laplacian (test η p) x + k^2*test η p x)) := by
    convert hJ.add (hI.const_mul (k^2)) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have ht := local_helmholtz_test hΩ u (test η p) hur hφ hφc hφs k heq
  rw [ComplexPolarIntegration.integral_polar_complex _ hi] at ht
  convert ht using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [ray_integrand u η hη p l hp hh k r hr, pow_add]
  ring

theorem weak_radial_polynomial (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (AnnularMoment.annulus R L))
    (heq : ∀ x, x ∈ AnnularMoment.annulus R L → laplacian u x + k^2*u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo R L) :
    (∫ r : ℝ, (r : ℂ)^(l+2) * moment u (angularPolynomial p) r * deriv (deriv η) r +
      (2*(l : ℂ)+2)*(r : ℂ)^(l+1) * moment u (angularPolynomial p) r * deriv η r +
      k^2*(r : ℂ)^(l+2) * moment u (angularPolynomial p) r * η r) = 0 := by
  let U := moment u (angularPolynomial p)
  have hz := weak_radial_equation R L hR k u hu heq p l hp hh η hη hc hs
  have he : (∫ r in Ioi (0 : ℝ),
      (r : ℂ)^(l+2)*U r*deriv (deriv η) r +
        (2*(l : ℂ)+2)*(r : ℂ)^(l+1)*U r*deriv η r +
        k^2*(r : ℂ)^(l+2)*U r*η r) =
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2)*U r*radialExpression l k η r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    simp only [radialExpression, pow_add, pow_one]
    field_simp [hn]
    ring
  have he' := he.trans hz
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at he'
  · exact he'
  · intro r hr
    have hn : r ∉ tsupport η := fun h => hr (lt_of_le_of_lt hR (hs h).1)
    have hv : η =ᶠ[𝓝 r] 0 := not_mem_tsupport_iff_eventuallyEq.mp hn
    have h1 : deriv η r = 0 := by simpa only [deriv_zero] using hv.deriv_eq
    have h2 : deriv (deriv η) r = 0 := by
      simpa only [deriv_zero] using hv.deriv.deriv_eq
    simp only [hv.eq_of_nhds, h1, h2, Pi.zero_apply, mul_zero, add_zero]

theorem weak_radial_real_test (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (AnnularMoment.annulus R L))
    (heq : ∀ x, x ∈ AnnularMoment.annulus R L → laplacian u x + k^2*u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo R L) :
    (∫ r : ℝ, (r : ℂ)^(l+2) * moment u (angularPolynomial p) r * ((deriv (deriv η) r : ℝ) : ℂ) +
      (2*(l : ℂ)+2)*(r : ℂ)^(l+1) * moment u (angularPolynomial p) r * ((deriv η r : ℝ) : ℂ) +
      k^2*(r : ℂ)^(l+2) * moment u (angularPolynomial p) r * (η r : ℂ)) = 0 := by
  have hδ : ContDiff ℝ (⊤ : ℕ∞) (fun r => (η r : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hη
  have hdη : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have he : deriv (fun r => (η r : ℂ)) = fun r => ((deriv η r : ℝ) : ℂ) :=
    funext (fun r => ((hη.differentiable (by simp) r).hasDerivAt.ofReal_comp).deriv)
  have he' : deriv (fun r => ((deriv η r : ℝ) : ℂ)) =
      fun r => ((deriv (deriv η) r : ℝ) : ℂ) :=
    funext (fun r => ((hdη.differentiable (by simp) r).hasDerivAt.ofReal_comp).deriv)
  have hsupport : tsupport (fun r => (η r : ℂ)) = tsupport η := by
    apply congrArg closure
    ext r
    exact not_congr Complex.ofReal_eq_zero
  have ht := weak_radial_polynomial R L hR k u hu heq p l hp hh
    (fun r => (η r : ℂ)) hδ (hc.comp_left (by simp : Complex.ofReal 0 = 0))
    (by rwa [hsupport])
  simpa only [he, he'] using ht

end OQ14.AnnularMomentEquation

#print axioms OQ14.AnnularMomentEquation.weak_radial_equation
#print axioms OQ14.AnnularMomentEquation.weak_radial_polynomial
#print axioms OQ14.AnnularMomentEquation.weak_radial_real_test

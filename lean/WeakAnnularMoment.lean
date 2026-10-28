import AnnularMomentEquation
import WeakHelmholtzRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.WeakAnnularMoment
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.RadialNormTest OQ14.HarmonicPolynomial
  OQ14.SphericalMomentEquation OQ14.RadialMoment OQ14.WeakHelmholtzRegularity
open scoped Topology

theorem integrable_mul_compact (u v : Space → ℂ) (hu : LocallyIntegrable u)
    (hv : Continuous v) (hc : HasCompactSupport v) : Integrable (fun x => u x*v x) := by
  have hk : IsCompact (tsupport v) := hc
  have h := (hu.integrableOn_isCompact hk).mul_continuousOn hv.continuousOn hk
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport v)]
  · exact h
  · intro x hx
    by_contra hn
    apply hx
    simp [image_eq_zero_of_nmem_tsupport hn]

theorem weak_radial_equation (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : LocallyIntegrable u)
    (heq : IsWeakHelmholtz k (AnnularMoment.annulus R L) u)
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
  have hlc : HasCompactSupport (laplacian (test η p)) := by
    apply hφc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (laplacian_zero_of_not_tsupport hn)
  have hi : Integrable (fun x => u x*(laplacian (test η p) x + k^2*test η p x)) := by
    apply integrable_mul_compact u _ hu
    · exact (laplacian_continuous hφ).add (continuous_const.mul hφ.continuous)
    · exact hlc.add (hφc.mul_left)
  have ht := heq (test η p) hφ hφc hφs
  rw [ComplexPolarIntegration.integral_polar_complex _ hi] at ht
  convert ht using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [ray_integrand u η hη p l hp hh k r hr, pow_add]
  ring

theorem weak_radial_polynomial (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : LocallyIntegrable u)
    (heq : IsWeakHelmholtz k (AnnularMoment.annulus R L) u)
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

#print axioms OQ14.WeakAnnularMoment.weak_radial_polynomial
#print axioms OQ14.WeakAnnularMoment.weak_radial_equation
end OQ14.WeakAnnularMoment



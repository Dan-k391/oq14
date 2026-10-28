import AnnularMomentEquation
import AnnularMomentClassical
import RadialMomentODE

/-! Complex Riccati basis expansion of actual Helmholtz moments on finite annuli. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.AnnularRiccatiBasis
open Complex Filter Set OQ14.RadialRellich OQ14.RadialMoment OQ14.RadialMomentODE
  OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
open scoped Topology

theorem two_solution_expansion (R L : ℝ) (f df u du v dv q : ℝ → ℂ) (W : ℂ)
    (hW : W ≠ 0)
    (hf : ∀ r ∈ Ioo R L, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L, HasDerivAt df (q r * f r) r)
    (hu : ∀ r ∈ Ioo R L, HasDerivAt u (du r) r)
    (hdu : ∀ r ∈ Ioo R L, HasDerivAt du (q r * u r) r)
    (hv : ∀ r ∈ Ioo R L, HasDerivAt v (dv r) r)
    (hdv : ∀ r ∈ Ioo R L, HasDerivAt dv (q r * v r) r)
    (hwr : ∀ r ∈ Ioo R L, u r * dv r - v r * du r = W) :
    ∃ a b : ℂ, ∀ r ∈ Ioo R L, f r = a * u r + b * v r := by
  let ac : ℝ → ℂ := fun r => (f r * dv r - v r * df r) / W
  let bc : ℝ → ℂ := fun r => (u r * df r - f r * du r) / W
  have ha (r : ℝ) (hr : r ∈ Ioo R L) : HasDerivAt ac 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt f df v dv q r (hf r hr) (hdf r hr) (hv r hr) (hdv r hr)).div_const W
  have hb (r : ℝ) (hr : r ∈ Ioo R L) : HasDerivAt bc 0 r := by
    simpa only [zero_div] using
      (ode_wronskian_hasDerivAt u du f df q r (hu r hr) (hdu r hr) (hf r hr) (hdf r hr)).div_const W
  obtain ⟨a, hae⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo R L).isPreconnected
    (fun r hr => (ha r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (ha r hr).deriv)
  obtain ⟨b, hbe⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo R L).isPreconnected
    (fun r hr => (hb r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hb r hr).deriv)
  refine ⟨a, b, ?_⟩
  intro r hr
  rw [← hae r hr, ← hbe r hr]
  dsimp only [ac, bc]
  field_simp [hW]
  linear_combination -f r * (hwr r hr)

theorem radial_expansion (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo R L, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo R L, HasDerivAt df (radialCoefficient l k r * f r) r) :
    ∃ a b : ℂ, ∀ r ∈ Ioo R L,
      f r = a * outgoing l k r + b * incoming l k r := by
  have hW : -2 * I * k ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hk
  exact two_solution_expansion R L f df _ _ _ _ _ _ hW hf hdf
    (fun r hr => outgoing_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr.1)))
    (fun r hr => outgoingD_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr.1)))
    (fun r hr => incoming_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr.1)))
    (fun r hr => incomingD_hasDerivAt l k hk r (ne_of_gt (lt_of_le_of_lt hR hr.1)))
    (fun r hr => radial_wronskian l k hk r (ne_of_gt (lt_of_le_of_lt hR hr.1)))

/-- Actual harmonic moments satisfy the two-mode expansion; radial equations are derived. -/
theorem helmholtz_moment_expansion (R L : ℝ) (hR : 0 ≤ R) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (AnnularMoment.annulus R L))
    (heq : ∀ x ∈ AnnularMoment.annulus R L, laplacian u x + k ^ 2 * u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ a b : ℂ, ∀ r ∈ Ioo R L,
      (r : ℂ) * moment u (SphericalMomentEquation.angularPolynomial p) r =
        a * outgoing l k r + b * incoming l k r := by
  let P := SphericalMomentEquation.angularPolynomial p
  have hP : Continuous P := SphericalMomentEquation.angularPolynomial_continuous p
  have hclass := AnnularMomentClassical.moment_classical_of_weak l k R L hR u hu P hP
    (fun η hη hc hs => AnnularMomentEquation.weak_radial_real_test R L hR k u hu heq p l hp hh η hη hc hs)
  let U := moment u P
  let F := RadialMomentClassical.radialFlux (momentD u P)
  apply radial_expansion l k hk R L hR (riccati U) (riccatiD U F)
  · intro r hr
    apply riccati_hasDerivAt U F r (ne_of_gt (lt_of_le_of_lt hR hr.1))
    exact (hclass r hr).2.2 ▸ AnnularMoment.moment_hasDerivAt R L r hR hr u hu P hP
  · intro r hr
    apply riccatiD_hasDerivAt l k U F r (ne_of_gt (lt_of_le_of_lt hR hr.1))
    · exact (hclass r hr).2.2 ▸ AnnularMoment.moment_hasDerivAt R L r hR hr u hu P hP
    · exact (hclass r hr).2.1

end OQ14.AnnularRiccatiBasis
#print axioms OQ14.AnnularRiccatiBasis.two_solution_expansion
#print axioms OQ14.AnnularRiccatiBasis.radial_expansion
#print axioms OQ14.AnnularRiccatiBasis.helmholtz_moment_expansion

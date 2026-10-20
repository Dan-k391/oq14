import AnnularMomentEquation
import AnnularMomentClassical
import RadialIntervalFlux
import HarmonicMomentSeparation

/-! # Genuine continuation of smooth Helmholtz fields inside a ball -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.HelmholtzBallContinuation

open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.AngularPower OQ14.RadialMoment OQ14.RadialMomentClassical
  OQ14.SphericalMomentEquation
open scoped Topology

theorem actual_annular_moment_equation (R L : ℝ) (hR : 0 ≤ R) (k : ℂ)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (AnnularMoment.annulus R L))
    (heq : ∀ x, x ∈ AnnularMoment.annulus R L → laplacian u x + k^2*u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ r ∈ Ioo R L,
      HasDerivAt (radialFlux (momentD u (angularPolynomial p)))
        (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*moment u (angularPolynomial p) r) r ∧
      momentD u (angularPolynomial p) r =
        radialFlux (momentD u (angularPolynomial p)) r/(r : ℂ)^2 := by
  have h := AnnularMomentClassical.moment_classical_of_weak l k R L hR u hu
    (angularPolynomial p) (angularPolynomial_continuous p) (fun η hη hc hs =>
      AnnularMomentEquation.weak_radial_real_test R L hR k u hu heq p l hp hh η hη hc hs)
  exact fun r hr => (h r hr).2

theorem moment_zero_near_small_radius (u : Space → ℂ) (hzero : u =ᶠ[𝓝 0] 0)
    (L : ℝ) (hL : 0 < L) :
    ∃ r₀ ∈ Ioo (0 : ℝ) L, ∀ P : Sphere → ℂ, moment u P =ᶠ[𝓝 r₀] 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hzero
  let r₀ := min ε L / 2
  have hp : 0 < r₀ := half_pos (lt_min hε hL)
  have he : r₀ < ε := by dsimp [r₀]; linarith [min_le_left ε L]
  have hl : r₀ < L := by dsimp [r₀]; linarith [min_le_right ε L]
  refine ⟨r₀, ⟨hp,hl⟩, ?_⟩
  intro P
  filter_upwards [isOpen_Ioo.mem_nhds (show r₀ ∈ Ioo (0 : ℝ) ε from ⟨hp,he⟩)] with r hr
  change moment u P r = 0
  unfold moment
  apply integral_eq_zero_of_ae
  filter_upwards with n
  have hn : r • (n : Space) ∈ ball (0 : Space) ε := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr.1, sphere_norm, mul_one] using hr.2
  have hz : u (r • (n : Space)) = 0 := hball hn
  simp only [hz, zero_mul, Pi.zero_apply]

theorem ball_harmonic_moments_zero (L : ℝ) (hL : 0 < L) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (ball 0 L))
    (heq : ∀ x ∈ ball (0 : Space) L, laplacian u x + k^2*u x = 0)
    (hzero : u =ᶠ[𝓝 0] 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∀ r ∈ Ioo (0 : ℝ) L, moment u (angularPolynomial p) r = 0 := by
  have hsub : AnnularMoment.annulus 0 L ⊆ ball (0 : Space) L :=
    fun x hx => by simpa only [mem_ball, dist_zero_right] using hx.2
  have h := actual_annular_moment_equation 0 L le_rfl k u (hu.mono hsub)
    (fun x hx => heq x (hsub hx)) p l hp hh
  obtain ⟨r₀,hr₀,hlocal⟩ := moment_zero_near_small_radius u hzero L hL
  have hz := RadialIntervalFlux.flux_zero_of_zero_neighborhood l k hk 0 L le_rfl
    (moment u (angularPolynomial p)) (radialFlux (momentD u (angularPolynomial p)))
    (fun r hr => (h r hr).2 ▸ AnnularMoment.moment_hasDerivAt 0 L r le_rfl hr
      u (hu.mono hsub) (angularPolynomial p) (angularPolynomial_continuous p))
    (fun r hr => (h r hr).1) r₀ hr₀ (hlocal (angularPolynomial p))
  exact fun r hr => (hz r hr).1

theorem zero_on_ball_of_zero_neighborhood (L : ℝ) (hL : 0 < L) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (ball 0 L))
    (heq : ∀ x ∈ ball (0 : Space) L, laplacian u x + k^2*u x = 0)
    (hzero : u =ᶠ[𝓝 0] 0) : ∀ x ∈ ball (0 : Space) L, u x = 0 := by
  have hz (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) :
      ∀ n : Sphere, u (r • (n : Space)) = 0 := by
    have hc : Continuous (fun n : Sphere => u (r • (n : Space))) := by
      apply continuous_iff_continuousAt.mpr
      intro n
      have hn : r • (n : Space) ∈ ball (0 : Space) L := by
        simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr.1, sphere_norm, mul_one] using hr.2
      exact (hu.continuousOn.continuousAt (isOpen_ball.mem_nhds hn)).comp
        (f := fun n : Sphere => r • (n : Space))
        (continuous_const.smul continuous_subtype_val).continuousAt
    apply HarmonicMomentSeparation.zero_of_harmonic_moments _ hc
    intro l p hp hh
    have h := ball_harmonic_moments_zero L hL k hk u hu heq hzero p l hp hh r hr
    simpa only [moment, angularPolynomial, HarmonicPolynomial.complexEvaluate,
      HarmonicPolynomial.evaluate, SpherePolynomial.polynomialMap_apply] using h
  intro x hx
  by_cases h0 : x = 0
  · subst x
    exact hzero.eq_of_nhds
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
    have hlt : ‖x‖ < L := by simpa only [mem_ball, dist_zero_right] using hx
    have hn : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (ne_of_gt hpos)]
    let n : Sphere := ⟨‖x‖⁻¹ • x, by simpa only [mem_sphere, dist_zero_right] using hn⟩
    have he : ‖x‖ • (n : Space) = x := by
      dsimp [n]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
    simpa only [he] using hz ‖x‖ ⟨hpos,hlt⟩ n

end OQ14.HelmholtzBallContinuation

#print axioms OQ14.HelmholtzBallContinuation.actual_annular_moment_equation
#print axioms OQ14.HelmholtzBallContinuation.moment_zero_near_small_radius
#print axioms OQ14.HelmholtzBallContinuation.ball_harmonic_moments_zero
#print axioms OQ14.HelmholtzBallContinuation.zero_on_ball_of_zero_neighborhood

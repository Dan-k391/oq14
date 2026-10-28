import AnnularRiccatiBasis
import RadialOriginSelection

/-! Origin regularity selects the regular Riccati solution for actual smooth ball moments. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RegularBallMoments
open Complex MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.RadialMoment
  OQ14.RadialRellich OQ14.ExteriorHelmholtz
open scoped Topology

theorem moment_continuous (u : Space → ℂ) (hu : Continuous u) (P : Sphere → ℂ)
    (hP : Continuous P) : Continuous (moment u P) := by
  have hj : Continuous (fun x : ℝ × Sphere => u (x.1 • (x.2 : Space)) * P x.2) :=
    (hu.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).mul
      (hP.comp continuous_snd)
  simpa only [moment, Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous hj isCompact_univ

theorem momentD_continuous (u : Space → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (P : Sphere → ℂ) (hP : Continuous P) : Continuous (momentD u P) := by
  have hj : Continuous (fun x : ℝ × Sphere =>
      (fderiv ℝ u (x.1 • (x.2 : Space))) (x.2 : Space) * P x.2) :=
    (((hu.continuous_fderiv (by simp)).comp
      (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).clm_apply
      (continuous_subtype_val.comp continuous_snd)).mul (hP.comp continuous_snd)
  simpa only [momentD, Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous hj isCompact_univ

theorem regular_moment (L : ℝ) (hL : 0 < L) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (heq : ∀ x ∈ ball (0 : Space) L, laplacian u x + k^2 * u x = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ r ∈ Ioo 0 L,
      (r : ℂ) * moment u (SphericalMomentEquation.angularPolynomial p) r =
        c * RadialOriginSelection.regular l k r := by
  let P := SphericalMomentEquation.angularPolynomial p
  have hP : Continuous P := SphericalMomentEquation.angularPolynomial_continuous p
  let U := moment u P
  let UD := momentD u P
  let f : ℝ → ℂ := fun r => (r : ℂ) * U r
  let df : ℝ → ℂ := fun r => U r + (r : ℂ) * UD r
  have hUc : Continuous U := moment_continuous u hu.continuous P hP
  have hUDc : Continuous UD := momentD_continuous u hu P hP
  have hf : Continuous f := Complex.continuous_ofReal.mul hUc
  have hdf : Continuous df := hUc.add (Complex.continuous_ofReal.mul hUDc)
  have hE : ∀ x ∈ AnnularMoment.annulus 0 L, laplacian u x + k^2 * u x = 0 :=
    fun x hx => heq x (by simpa only [mem_ball, dist_zero_right] using hx.2)
  have hclass := AnnularMomentClassical.moment_classical_of_weak l k 0 L (by norm_num) u hu.contDiffOn P hP
    (fun η hη hc hs => AnnularMomentEquation.weak_radial_real_test 0 L (by norm_num) k u hu.contDiffOn hE p l hp hh η hη hc hs)
  apply RadialOriginSelection.regular_selection l k hk L hL f df hf.continuousAt hdf.continuousAt
    (by simp [f])
  · intro r hr
    have hd := (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
    convert hd.mul (AnnularMoment.moment_hasDerivAt 0 L r (by norm_num) hr u hu.contDiffOn P hP) using 1
    simp [df, U, UD]
  · intro r hr
    let F := RadialMomentClassical.radialFlux UD
    have hU : HasDerivAt U (F r / (r : ℂ)^2) r :=
      (hclass r hr).2.2 ▸ AnnularMoment.moment_hasDerivAt 0 L r (by norm_num) hr u hu.contDiffOn P hP
    have hd := RadialMomentODE.riccatiD_hasDerivAt l k U F r hr.1.ne' hU (hclass r hr).2.1
    have he : df =ᶠ[𝓝 r] RadialMomentODE.riccatiD U F := by
      filter_upwards [eventually_ne_nhds hr.1.ne'] with t ht
      dsimp [df, RadialMomentODE.riccatiD, F, RadialMomentClassical.radialFlux]
      field_simp [Complex.ofReal_ne_zero.mpr ht]
      ring
    exact hd.congr_of_eventuallyEq he

end OQ14.RegularBallMoments
#print axioms OQ14.RegularBallMoments.moment_continuous
#print axioms OQ14.RegularBallMoments.momentD_continuous
#print axioms OQ14.RegularBallMoments.regular_moment

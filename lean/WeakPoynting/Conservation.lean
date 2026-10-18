import WeakPoynting.Local

/-!
# Real local power conservation for weak Maxwell fields

Permittivity and permeability are real functions and the actual L2 weak curls
satisfy Maxwell's equations almost everywhere. No coefficient differentiability,
field differentiability, global L2 condition, or boundary condition is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.WeakConservation

open MeasureTheory OQ14.Maxwell OQ14.LocalPower
open scoped ComplexConjugate Topology

structure RealTest (Ω : Set Space) where
  function : Space → ℝ
  regular : ContDiff ℝ 1 function
  compact : HasCompactSupport function
  inside : tsupport function ⊆ Ω

def RealTest.complexTest {Ω : Set Space} (χ : RealTest Ω) : DomainCurl.Test Ω where
  function := fun x => (χ.function x : ℂ)
  regular := Complex.ofRealCLM.contDiff.comp χ.regular
  compact := χ.compact.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  inside := by simpa only [tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using χ.inside

theorem realTest_partial {Ω : Set Space} (χ : RealTest Ω) (x : Space) (j : Fin 3) :
    dcoord χ.complexTest.function x j = (fderiv ℝ χ.function x (basis j) : ℂ) := by
  have hh := (Complex.ofRealCLM.hasFDerivAt.comp x
    (χ.regular.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (basis j)) hh
  simpa [dcoord, RealTest.complexTest, Function.comp_def] using hv

/-- The algebraic reactive term follows from the actual two curl equations. -/
theorem reactive_algebra (ω μ ε : ℝ) (E C H K : Vector)
    (hC : ∀ j, C j = Complex.I * ω * μ * H j)
    (hK : ∀ j, K j = -Complex.I * ω * ε * E j) :
    dot C (conjugate H) - dot E (conjugate K) =
      Complex.I * ω * ((μ : ℂ) * energy H - (ε : ℂ) * energy E) := by
  have hEE := dot_conjugate E
  have hHH := dot_conjugate H
  dsimp [dot, conjugate] at hEE hHH ⊢
  simp only [hC, hK, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (Complex.I * ω * μ) * hHH - (Complex.I * ω * ε) * hEE

/-- The real Poynting vector, with the conventional time-average factor 1/2. -/
def realPower (E H : Field) (x : Space) (j : Fin 3) : ℝ :=
  (crossProduct (E x) (conjugate (H x)) j).re / 2

/-- Pairing of grad χ with the real Poynting vector. -/
def testPower {Ω : Set Space} (χ : RealTest Ω) (E H : Field) (x : Space) : ℝ :=
  fderiv ℝ χ.function x (basis 0) * realPower E H x 0 +
  fderiv ℝ χ.function x (basis 1) * realPower E H x 1 +
  fderiv ℝ χ.function x (basis 2) * realPower E H x 2

theorem density_real_part {Ω : Set Space} (χ : RealTest Ω) (E C H K : Field)
    (ω : ℝ) (μ ε : Space → ℝ) (x : Space)
    (hC : ∀ j, C x j = Complex.I * ω * μ x * H x j)
    (hK : ∀ j, K x j = -Complex.I * ω * ε x * E x j) :
    (density χ.complexTest.toTest E C H K x).re = 2 * testPower χ E H x := by
  unfold density
  rw [reactive_algebra ω (μ x) (ε x) (E x) (C x) (H x) (K x) hC hK]
  rw [show χ.complexTest.function x = (χ.function x : ℂ) from rfl]
  simp only [dot, realTest_partial, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, Complex.sub_re, Complex.sub_im,
    Complex.mul_im, zero_add]
  dsimp [testPower, realPower]
  ring

/-- Actual almost-everywhere source-free Maxwell equations for regional H(curl) fields.
The coefficients may be discontinuous; the equations refer to genuine weak curls. -/
def WeakMaxwell {Ω : Set Space} (ω : ℝ) (μ ε : Space → ℝ)
    (E H : DomainCurl.HCurl Ω) : Prop :=
  (∀ᵐ x ∂DomainCurl.regionMeasure Ω,
    ∀ j, E.val.2 j x = Complex.I * ω * μ x * H.val.1 j x) ∧
  (∀ᵐ x ∂DomainCurl.regionMeasure Ω,
    ∀ j, H.val.2 j x = -Complex.I * ω * ε x * E.val.1 j x)

theorem weakMaxwell_density_ae {Ω : Set Space} (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    (fun x => (density χ.complexTest.toTest (fun y j => E.val.1 j y)
      (fun y j => E.val.2 j y) (fun y j => H.val.1 j y) (fun y j => H.val.2 j y) x).re)
      =ᵐ[DomainCurl.regionMeasure Ω]
    (fun x => 2 * testPower χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) := by
  filter_upwards [hM.1, hM.2] with x hc hk
  exact density_real_part χ _ _ _ _ ω μ ε x hc hk

/-- The real flux pairing is integrable, derived from genuine L2 field/curl products. -/
theorem weak_real_power_integrable {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    Integrable (testPower χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y))
      (DomainCurl.regionMeasure Ω) := by
  have hi := (local_poyntingDensity_integrable hΩ χ.complexTest E H).re
  have ht := (hi.congr (weakMaxwell_density_ae χ ω μ ε E H hM)).const_mul (1 / 2 : ℝ)
  convert ht using 1
  ext x
  ring

/-- Real local power has zero distributional divergence on an arbitrary open region.
This is proved for weak Maxwell fields, with variable real coefficients and real compact C1 tests. -/
theorem weak_real_power_conservation {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    (∫ x in Ω, testPower χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) = 0 := by
  have hi := local_poyntingDensity_integrable hΩ χ.complexTest E H
  have hz := congrArg Complex.re (local_weak_complex_Poynting hΩ χ.complexTest E H)
  rw [← RCLike.re_eq_complex_re, ← integral_re hi] at hz
  simp only [RCLike.re_eq_complex_re, Complex.zero_re] at hz
  rw [integral_congr_ae (weakMaxwell_density_ae χ ω μ ε E H hM), integral_const_mul] at hz
  simpa using (mul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℝ) ≠ 0)

end OQ14.WeakConservation

#print axioms OQ14.WeakConservation.realTest_partial
#print axioms OQ14.WeakConservation.reactive_algebra
#print axioms OQ14.WeakConservation.density_real_part
#print axioms OQ14.WeakConservation.weakMaxwell_density_ae
#print axioms OQ14.WeakConservation.weak_real_power_integrable
#print axioms OQ14.WeakConservation.weak_real_power_conservation

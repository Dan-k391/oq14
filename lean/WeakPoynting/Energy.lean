import WeakPoynting.LipschitzBoundary

/-! # Actual regional weak Maxwell energy identities and cutoff estimates -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.WeakEnergy

open MeasureTheory OQ14.Maxwell OQ14.WeakConservation OQ14.LocalPower Filter
open scoped Topology ComplexConjugate

theorem energy_nonneg (v : Vector) : 0 ≤ energy v := by
  exact add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (Complex.normSq_nonneg _)

theorem energy_integrable {Ω : Set Space} (u : DomainCurl.L2Vector Ω) :
    Integrable (fun x => energy (fun j => u j x)) (DomainCurl.regionMeasure Ω) := by
  have hi (j : Fin 3) : Integrable (fun x => Complex.normSq (u j x)) (DomainCurl.regionMeasure Ω) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (u j) (u j)).re.congr
    exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, Complex.normSq_apply])
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem conjugate_product_integrable {Ω : Set Space} (u v : DomainCurl.L2Scalar Ω) :
    Integrable (fun x => u x * conj (v x)) (DomainCurl.regionMeasure Ω) := by
  simpa only [RCLike.inner_apply] using L2.integrable_inner (𝕜 := ℂ) v u

theorem coefficient_energy_integrable {Ω : Set Space} (u : DomainCurl.L2Vector Ω)
    (c : Space → ℝ) (hc : AEStronglyMeasurable c (DomainCurl.regionMeasure Ω))
    (hb : ∃ M, ∀ x, ‖c x‖ ≤ M) :
    Integrable (fun x => c x * energy (fun j => u j x)) (DomainCurl.regionMeasure Ω) :=
  (energy_integrable u).bdd_mul hc hb

def reactiveFlux {Ω : Set Space} (χ : RealTest Ω) (E H : Field) (x : Space) : ℝ :=
  fderiv ℝ χ.function x (basis 0) * (crossProduct (E x) (conjugate (H x)) 0).im +
  fderiv ℝ χ.function x (basis 1) * (crossProduct (E x) (conjugate (H x)) 1).im +
  fderiv ℝ χ.function x (basis 2) * (crossProduct (E x) (conjugate (H x)) 2).im

theorem reactiveFlux_integrable {Ω : Set Space} (χ : RealTest Ω)
    (E H : DomainCurl.L2Vector Ω) :
    Integrable (reactiveFlux χ (fun x j => E j x) (fun x j => H j x))
      (DomainCurl.regionMeasure Ω) := by
  have hp (i j k : Fin 3) : Integrable (fun x =>
      fderiv ℝ χ.function x (basis i) * (E j x * conj (H k x)).im)
      (DomainCurl.regionMeasure Ω) := by
    have hd := (χ.regular.continuous_fderiv le_rfl).clm_apply (continuous_const (y := basis i))
    exact (conjugate_product_integrable (E j) (H k)).im.bdd_mul hd.aestronglyMeasurable
      (hd.bounded_above_of_compact_support (χ.compact.fderiv_apply ℝ (basis i)))
  convert (((hp 0 1 2).sub (hp 0 2 1)).add ((hp 1 2 0).sub (hp 1 0 2))).add
    ((hp 2 0 1).sub (hp 2 1 0)) using 1
  ext x
  simp only [reactiveFlux, conjugate, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.sub_im, Pi.add_apply, Pi.sub_apply]
  ring

theorem density_imaginary_part {Ω : Set Space} (χ : RealTest Ω) (E C H K : Field)
    (ω : ℝ) (μ ε : Space → ℝ) (x : Space)
    (hC : ∀ j, C x j = Complex.I * ω * μ x * H x j)
    (hK : ∀ j, K x j = -Complex.I * ω * ε x * E x j) :
    (density χ.complexTest.toTest E C H K x).im =
      χ.function x * ω * (μ x * energy (H x) - ε x * energy (E x)) + reactiveFlux χ E H x := by
  unfold density
  rw [reactive_algebra ω (μ x) (ε x) (E x) (C x) (H x) (K x) hC hK]
  rw [show χ.complexTest.function x = (χ.function x : ℂ) from rfl]
  simp only [dot, realTest_partial, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
    mul_zero, sub_zero, add_zero, Complex.sub_re, Complex.sub_im, zero_add]
  dsimp [reactiveFlux]
  ring

theorem weakMaxwell_imaginary_density_ae {Ω : Set Space} (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    (fun x => (density χ.complexTest.toTest (fun y j => E.val.1 j y)
      (fun y j => E.val.2 j y) (fun y j => H.val.1 j y) (fun y j => H.val.2 j y) x).im)
      =ᵐ[DomainCurl.regionMeasure Ω]
    (fun x => χ.function x * ω * (μ x * energy (fun j => H.val.1 j x) -
      ε x * energy (fun j => E.val.1 j x)) +
      reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) := by
  filter_upwards [hM.1, hM.2] with x hc hk
  exact density_imaginary_part χ _ _ _ _ ω μ ε x hc hk

/-- The reactive identity is derived from the actual regional complex weak law. -/
theorem weak_energy_identity {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    (∫ x in Ω, χ.function x * ω * (μ x * energy (fun j => H.val.1 j x) -
      ε x * energy (fun j => E.val.1 j x)) +
      reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) = 0 := by
  have hi := local_poyntingDensity_integrable hΩ χ.complexTest E H
  have hz := congrArg Complex.im (local_weak_complex_Poynting hΩ χ.complexTest E H)
  rw [← RCLike.im_eq_complex_im, ← integral_im hi] at hz
  simp only [RCLike.im_eq_complex_im, Complex.zero_im] at hz
  rwa [integral_congr_ae (weakMaxwell_imaginary_density_ae χ ω μ ε E H hM)] at hz

theorem weak_energy_density_integrable {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    Integrable (fun x => χ.function x * ω * (μ x * energy (fun j => H.val.1 j x) -
      ε x * energy (fun j => E.val.1 j x)) +
      reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x)
      (DomainCurl.regionMeasure Ω) :=
  (local_poyntingDensity_integrable hΩ χ.complexTest E H).im.congr
    (weakMaxwell_imaginary_density_ae χ ω μ ε E H hM)

theorem weighted_energy_integrable {Ω : Set Space} (χ : RealTest Ω)
    (u : DomainCurl.L2Vector Ω) :
    Integrable (fun x => χ.function x * energy (fun j => u j x)) (DomainCurl.regionMeasure Ω) :=
  (energy_integrable u).bdd_mul χ.regular.continuous.aestronglyMeasurable
    (χ.regular.continuous.bounded_above_of_compact_support χ.compact)

/-- At nonzero frequency, the electric energy weight is integrable directly
from the actual curl equations, without a separate coefficient bound. -/
theorem weighted_electric_integrable {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) :
    Integrable (fun x => χ.function x * ε x * energy (fun j => E.val.1 j x))
      (DomainCurl.regionMeasure Ω) := by
  have hi := weak_energy_density_integrable hΩ χ ω (fun _ => 1) ε E H hM
  have hj := reactiveFlux_integrable χ E.val.1 H.val.1
  have hk := weighted_energy_integrable χ H.val.1
  convert (((hk.const_mul ω).add hj).sub hi).div_const ω using 1
  ext x
  dsimp only [Pi.sub_apply, Pi.add_apply]
  field_simp
  ring

/-- Genuine weighted electric/magnetic balance, with all three terms integrable. -/
theorem weighted_energy_balance {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) :
    ω * (∫ x in Ω, χ.function x * ε x * energy (fun j => E.val.1 j x)) =
      ω * (∫ x in Ω, χ.function x * energy (fun j => H.val.1 j x)) +
        ∫ x in Ω, reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x := by
  have he := weighted_electric_integrable hΩ χ ω hω ε E H hM
  have hh := weighted_energy_integrable χ H.val.1
  have hr := reactiveFlux_integrable χ E.val.1 H.val.1
  have hz := weak_energy_identity hΩ χ ω (fun _ => 1) ε E H hM
  have hi : (∫ x in Ω, χ.function x * ω * (1 * energy (fun j => H.val.1 j x) -
      ε x * energy (fun j => E.val.1 j x)) +
      reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) =
      (∫ x in Ω, ω * (χ.function x * energy (fun j => H.val.1 j x)) -
        ω * (χ.function x * ε x * energy (fun j => E.val.1 j x)) +
          reactiveFlux χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y) x) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  have hdiff : Integrable (fun x => ω * (χ.function x * energy (fun j => H.val.1 j x)) -
      ω * (χ.function x * ε x * energy (fun j => E.val.1 j x)))
      (DomainCurl.regionMeasure Ω) := (hh.const_mul ω).sub (he.const_mul ω)
  rw [hi, integral_add hdiff hr,
    integral_sub (hh.const_mul ω) (he.const_mul ω), integral_const_mul, integral_const_mul] at hz
  linarith

def realEnergy (g : Fin 3 → ℝ) : ℝ := g 0 ^ 2 + g 1 ^ 2 + g 2 ^ 2
def realLift (g : Fin 3 → ℝ) : Vector := fun j => (g j : ℂ)

theorem real_cross_energy (g : Fin 3 → ℝ) (H : Vector) :
    energy (crossProduct (realLift g) H) + Complex.normSq (dot (realLift g) H) =
      realEnergy g * energy H := by
  simp [energy, realEnergy, realLift, dot, cross_apply, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem real_cross_energy_le (g : Fin 3 → ℝ) (H : Vector) :
    energy (crossProduct (realLift g) H) ≤ realEnergy g * energy H := by
  have hh := real_cross_energy g H
  have hn := Complex.normSq_nonneg (dot (realLift g) H)
  linarith

theorem cutoff_young_scaled (ω m ζ : ℝ) (g : Fin 3 → ℝ) (E H : Vector) :
    4 * ω * m * ζ * (dot (realLift g) (crossProduct E (conjugate H))).im ≤
      ω ^ 2 * m ^ 2 * ζ ^ 2 * energy E + 4 * realEnergy g * energy H := by
  have hn := energy_nonneg (fun j => ((ω * m * ζ : ℝ) : ℂ) * E j +
    2 * Complex.I * crossProduct (realLift g) H j)
  have he : energy (fun j => ((ω * m * ζ : ℝ) : ℂ) * E j +
      2 * Complex.I * crossProduct (realLift g) H j) =
      ω ^ 2 * m ^ 2 * ζ ^ 2 * energy E + 4 * energy (crossProduct (realLift g) H) -
        4 * ω * m * ζ * (dot (realLift g) (crossProduct E (conjugate H))).im := by
    simp [energy, realLift, dot, conjugate, cross_apply, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  rw [he] at hn
  have hc := real_cross_energy_le g H
  linarith

def squareTest {Ω : Set Space} (ζ : RealTest Ω) : RealTest Ω where
  function := fun x => ζ.function x ^ 2
  regular := ζ.regular.pow 2
  compact := by
    have h : HasCompactSupport (fun x => ζ.function x * ζ.function x) := ζ.compact.mul_right
    simpa only [pow_two] using h
  inside := by simpa only [pow_two] using
    (tsupport_mul_subset_left (f := ζ.function) (g := ζ.function)).trans ζ.inside

def gradient {Ω : Set Space} (ζ : RealTest Ω) (x : Space) (j : Fin 3) : ℝ :=
  fderiv ℝ ζ.function x (basis j)

theorem squareTest_partial {Ω : Set Space} (ζ : RealTest Ω) (x : Space) (j : Fin 3) :
    fderiv ℝ (squareTest ζ).function x (basis j) = 2 * ζ.function x * gradient ζ x j := by
  have hd := (ζ.regular.differentiable le_rfl x).hasFDerivAt
  have he := congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) (hd.mul hd).fderiv
  simpa [squareTest, pow_two, gradient, mul_comm, mul_left_comm, mul_assoc,
    two_mul, add_mul] using he

theorem squareTest_reactive {Ω : Set Space} (ζ : RealTest Ω) (E H : Field) (x : Space) :
    reactiveFlux (squareTest ζ) E H x = 2 * ζ.function x *
      (dot (realLift (gradient ζ x)) (crossProduct (E x) (conjugate (H x)))).im := by
  simp only [reactiveFlux, squareTest_partial, dot, realLift, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem gradient_energy_integrable {Ω : Set Space} (ζ : RealTest Ω)
    (u : DomainCurl.L2Vector Ω) :
    Integrable (fun x => realEnergy (gradient ζ x) * energy (fun j => u j x))
      (DomainCurl.regionMeasure Ω) := by
  have hc (j : Fin 3) : Continuous (fun x => gradient ζ x j) :=
    (ζ.regular.continuous_fderiv le_rfl).clm_apply (continuous_const (y := basis j))
  have hs (j : Fin 3) : HasCompactSupport (fun x => gradient ζ x j) :=
    ζ.compact.fderiv_apply ℝ (basis j)
  have hreg : Continuous (fun x => realEnergy (gradient ζ x)) :=
    (((hc 0).pow 2).add ((hc 1).pow 2)).add ((hc 2).pow 2)
  have hsup : HasCompactSupport (fun x => realEnergy (gradient ζ x)) := by
    have hsq (j : Fin 3) : HasCompactSupport (fun x => gradient ζ x j * gradient ζ x j) :=
      (hs j).mul_right
    simpa only [realEnergy, pow_two] using ((hsq 0).add (hsq 1)).add (hsq 2)
  exact (energy_integrable u).bdd_mul hreg.aestronglyMeasurable
    (hreg.bounded_above_of_compact_support hsup)

/-- Caccioppoli's weighted electric-energy estimate for actual regional weak
Maxwell fields, with the standard two-term Young constants and no derivative of ε. -/
theorem caccioppoli {Ω : Set Space} (hΩ : IsOpen Ω) (ζ : RealTest Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) (m : ℝ) (hm : 0 < m)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x) :
    (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) ≤
      2 * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) +
        4 / (ω ^ 2 * m) *
          (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => H.val.1 j x)) := by
  have he := weighted_electric_integrable hΩ (squareTest ζ) ω hω ε E H hM
  have hh := weighted_energy_integrable (squareTest ζ) H.val.1
  have hr := reactiveFlux_integrable (squareTest ζ) E.val.1 H.val.1
  have hg := gradient_energy_integrable ζ H.val.1
  have hb := weighted_energy_balance hΩ (squareTest ζ) ω hω ε E H hM
  dsimp only [squareTest] at he hh hb
  have hp : ∀ᵐ x ∂DomainCurl.regionMeasure Ω,
      2 * ω * m * reactiveFlux (squareTest ζ) (fun y j => E.val.1 j y)
        (fun y j => H.val.1 j y) x ≤
      ω ^ 2 * m * (ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) +
        4 * (realEnergy (gradient ζ x) * energy (fun j => H.val.1 j x)) := by
    filter_upwards [hε] with x hx
    rw [squareTest_reactive]
    have hy := cutoff_young_scaled ω m (ζ.function x) (gradient ζ x)
      (fun j => E.val.1 j x) (fun j => H.val.1 j x)
    have hc := mul_le_mul_of_nonneg_left hx
      (show 0 ≤ ω ^ 2 * m * ζ.function x ^ 2 * energy (fun j => E.val.1 j x) by
        exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg ω) hm.le)
          (sq_nonneg _)) (energy_nonneg _))
    nlinarith
  have hi := integral_mono_ae (hr.const_mul (2 * ω * m))
    ((he.const_mul (ω ^ 2 * m)).add (hg.const_mul 4)) hp
  dsimp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (he.const_mul (ω ^ 2 * m)) (hg.const_mul 4),
    integral_const_mul, integral_const_mul] at hi
  have hb2 := congrArg (fun r : ℝ => 2 * ω * m * r) hb
  dsimp only [DomainCurl.regionMeasure, squareTest] at hi hb2
  have hpos : 0 < ω ^ 2 * m := mul_pos (sq_pos_of_ne_zero hω) hm
  have hscaled : (ω ^ 2 * m) *
      (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) ≤
      (ω ^ 2 * m) * (2 * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x))) +
        4 * (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => H.val.1 j x)) := by
    nlinarith [hi, hb2]
  apply (mul_le_mul_left hpos).mp
  calc
    _ ≤ _ := hscaled
    _ = _ := by field_simp; ring

end OQ14.WeakEnergy

#print axioms OQ14.WeakEnergy.energy_integrable
#print axioms OQ14.WeakEnergy.reactiveFlux_integrable
#print axioms OQ14.WeakEnergy.weak_energy_identity
#print axioms OQ14.WeakEnergy.real_cross_energy
#print axioms OQ14.WeakEnergy.cutoff_young_scaled
#print axioms OQ14.WeakEnergy.weighted_electric_integrable
#print axioms OQ14.WeakEnergy.weighted_energy_balance
#print axioms OQ14.WeakEnergy.squareTest_reactive
#print axioms OQ14.WeakEnergy.gradient_energy_integrable
#print axioms OQ14.WeakEnergy.caccioppoli

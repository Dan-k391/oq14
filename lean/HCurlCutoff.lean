import HCurlDomain

/-!
# Cutoff multiplication for actual distributional H(curl) fields

The scalar multiplier is compactly supported and C1. Its value and first
derivatives are bounded, so all products below are actual L2 classes.
The curl product rule is derived from the weak equation and the classical
product rule for test functions, without differentiability of the field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.CurlCutoff

open MeasureTheory OQ14.Maxwell OQ14.DomainCurl
open scoped ComplexConjugate Topology

variable (Ω : Set Space)

theorem multiplier_memLp (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) :
    MemLp (fun x => f x * u x) 2 (regionMeasure Ω) :=
  (Lp.memLp u).mul' (hf.memLp_of_hasCompactSupport hc : MemLp f ⊤ (regionMeasure Ω))

def mulL2 (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) : L2Scalar Ω :=
  (multiplier_memLp Ω f hf hc u).toLp (fun x => f x * u x)

theorem mulL2_ae (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) :
    (fun x => mulL2 Ω f hf hc u x) =ᵐ[regionMeasure Ω] (fun x => f x * u x) :=
  (multiplier_memLp Ω f hf hc u).coeFn_toLp

theorem mulL2_norm_le (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u : L2Scalar Ω) {A : ℝ}
    (hA : ∀ x, ‖f x‖ ≤ A) : ‖mulL2 Ω f hf hc u‖ ≤ A * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulL2_ae Ω f hf hc u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

def multiply (χ : WeakCurl.Test) (E : L2Vector Ω) : L2Vector Ω :=
  fun j => mulL2 Ω χ.function χ.regular.continuous χ.compact (E j)

def derivativeMultiply (χ : WeakCurl.Test) (i : Fin 3) (u : L2Scalar Ω) : L2Scalar Ω :=
  mulL2 Ω (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
    (χ.compact.fderiv_apply ℝ (basis i)) u

/-- The literal L2 formula χ curl E + grad χ × E. -/
def productCurl (χ : WeakCurl.Test) (E C : L2Vector Ω) : L2Vector Ω :=
  fun j => multiply Ω χ C j +
    derivativeMultiply Ω χ (WeakCurl.next j) (E (WeakCurl.previous j)) -
    derivativeMultiply Ω χ (WeakCurl.previous j) (E (WeakCurl.next j))

def productTest (χ : WeakCurl.Test) (φ : Test Ω) : Test Ω where
  function := fun x => χ.function x * φ.function x
  regular := χ.regular.mul φ.regular
  compact := χ.compact.mul_right
  inside := tsupport_mul_subset_right.trans φ.inside

def outerProductTest (χ : Test Ω) (φ : WeakCurl.Test) : Test Ω where
  function := fun x => χ.function x * φ.function x
  regular := χ.regular.mul φ.regular
  compact := χ.compact.mul_right
  inside := tsupport_mul_subset_left.trans χ.inside

theorem testPair_mulL2 (f g : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : L2Scalar Ω) :
    testPair Ω g hg hgc (mulL2 Ω f hf hc u) =
      testPair Ω (fun x => f x * g x) (hf.mul hg) hc.mul_right u := by
  rw [testPair_integral, testPair_integral]
  apply integral_congr_ae
  filter_upwards [mulL2_ae Ω f hf hc u] with x hx
  rw [hx]
  ring

theorem valuePair_product (χ : WeakCurl.Test) (φ : Test Ω) (u : L2Scalar Ω) :
    valuePair Ω (productTest Ω χ φ) u =
      valuePair Ω φ (mulL2 Ω χ.function χ.regular.continuous χ.compact u) := by
  exact (testPair_mulL2 Ω χ.function φ.function χ.regular.continuous χ.compact
    φ.regular.continuous φ.compact u).symm

theorem derivative_pairing_product (χ φ : WeakCurl.Test)
    (i : Fin 3) (u : L2Scalar Ω) :
    testPair Ω (fun x => dcoord (fun y => χ.function y * φ.function y) x i)
        (partial_continuous (χ.regular.mul φ.regular) i)
        ((χ.compact.mul_right).fderiv_apply ℝ (basis i)) u =
      testPair Ω (fun x => dcoord φ.function x i) (partial_continuous φ.regular i)
        (φ.compact.fderiv_apply ℝ (basis i))
        (mulL2 Ω χ.function χ.regular.continuous χ.compact u) +
      testPair Ω φ.function φ.regular.continuous φ.compact
        (derivativeMultiply Ω χ i u) := by
  simp only [derivativeMultiply]
  rw [testPair_mulL2, testPair_mulL2]
  simp only [testPair_integral]
  have h₁ := testPair_integrable Ω
    (fun x => χ.function x * dcoord φ.function x i)
    (χ.regular.continuous.mul (partial_continuous φ.regular i)) χ.compact.mul_right u
  have h₂ := testPair_integrable Ω
    (fun x => dcoord χ.function x i * φ.function x)
    ((partial_continuous χ.regular i).mul φ.regular.continuous)
    (χ.compact.fderiv_apply ℝ (basis i)).mul_right u
  rw [← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [partial_mul (χ.regular.differentiable (by norm_num) x)
    (φ.regular.differentiable (by norm_num) x)]
  ring

theorem derivativePair_product (χ : WeakCurl.Test) (φ : Test Ω)
    (i : Fin 3) (u : L2Scalar Ω) :
    derivativePair Ω (productTest Ω χ φ) i u =
      derivativePair Ω φ i (mulL2 Ω χ.function χ.regular.continuous χ.compact u) +
      valuePair Ω φ (derivativeMultiply Ω χ i u) :=
  derivative_pairing_product Ω χ φ.toTest i u

/-- Distributional curl product rule for arbitrary weak L2 fields. -/
theorem weakCurl_multiply (χ : WeakCurl.Test) {E C : L2Vector Ω}
    (h : HasWeakCurl Ω E C) :
    HasWeakCurl Ω (multiply Ω χ E) (productCurl Ω χ E C) := by
  intro φ j
  have hh := h (productTest Ω χ φ) j
  change weakCurl Ω (productTest Ω χ φ) j E -
    valuePair Ω (productTest Ω χ φ) (C j) = 0 at hh
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, derivativePair_product, valuePair_product] at hh
  change weakCurl Ω φ j (multiply Ω χ E) - valuePair Ω φ (productCurl Ω χ E C j) = 0
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, productCurl, map_sub, map_add, multiply]
  linear_combination hh

theorem multiply_norm_le (χ : WeakCurl.Test) (E : L2Vector Ω) {A : ℝ}
    (hA : 0 ≤ A) (hχ : ∀ x, ‖χ.function x‖ ≤ A) :
    ‖multiply Ω χ E‖ ≤ A * ‖E‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA (norm_nonneg _))).mpr
  intro j
  exact (mulL2_norm_le Ω χ.function χ.regular.continuous χ.compact (E j) hχ).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm E j) hA)

theorem productCurl_norm_le (χ : WeakCurl.Test) (E C : L2Vector Ω) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hχ : ∀ x, ‖χ.function x‖ ≤ A)
    (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B) :
    ‖productCurl Ω χ E C‖ ≤ A * ‖C‖ + 2 * B * ‖E‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hv : ‖multiply Ω χ C j‖ ≤ A * ‖C‖ :=
    (norm_le_pi_norm (multiply Ω χ C) j).trans (multiply_norm_le Ω χ C hA hχ)
  have hd (i l : Fin 3) : ‖derivativeMultiply Ω χ i (E l)‖ ≤ B * ‖E‖ :=
    (mulL2_norm_le Ω _ (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) (E l) (hdχ i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm E l) hB)
  exact (norm_sub_le _ _).trans
    ((add_le_add_right (norm_add_le _ _) _).trans (by
      linarith [hd (WeakCurl.next j) (WeakCurl.previous j),
        hd (WeakCurl.previous j) (WeakCurl.next j)]))

def cutoff (χ : WeakCurl.Test) (u : HCurl Ω) : HCurl Ω :=
  ⟨(multiply Ω χ u.val.1, productCurl Ω χ u.val.1 u.val.2),
    weakCurl_multiply Ω χ u.property⟩

/-- A quantitative graph-norm bound, with coordinatewise derivative bound B. -/
theorem cutoff_norm_le (χ : WeakCurl.Test) (u : HCurl Ω) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hχ : ∀ x, ‖χ.function x‖ ≤ A)
    (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B) :
    ‖cutoff Ω χ u‖ ≤ (A + 2 * B) * ‖u‖ := by
  rw [graph_norm]
  apply max_le
  · have h := multiply_norm_le Ω χ u.val.1 hA hχ
    have he : ‖u.val.1‖ ≤ ‖u‖ := le_max_left _ _
    dsimp only [cutoff]
    nlinarith [norm_nonneg u]
  · have h := productCurl_norm_le Ω χ u.val.1 u.val.2 hA hB hχ hdχ
    have he : ‖u.val.1‖ ≤ ‖u‖ := le_max_left _ _
    have hc : ‖u.val.2‖ ≤ ‖u‖ := le_max_right _ _
    dsimp only [cutoff]
    nlinarith

/-- Zero extension of a restricted-measure L2 class, represented by the indicator. -/
def extendScalar (hΩ : MeasurableSet Ω) (u : L2Scalar Ω) : WeakCurl.L2Scalar :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)).toLp (Ω.indicator u)

theorem extendScalar_ae (hΩ : MeasurableSet Ω) (u : L2Scalar Ω) :
    (fun x => extendScalar Ω hΩ u x) =ᵐ[volume] Ω.indicator u :=
  ((memLp_indicator_iff_restrict hΩ).mpr (Lp.memLp u)).coeFn_toLp

theorem extendScalar_norm (hΩ : MeasurableSet Ω) (u : L2Scalar Ω) :
    ‖extendScalar Ω hΩ u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (extendScalar_ae Ω hΩ u),
    eLpNorm_indicator_eq_eLpNorm_restrict hΩ]

def extendVector (hΩ : MeasurableSet Ω) (E : L2Vector Ω) : WeakCurl.L2Vector :=
  fun j => extendScalar Ω hΩ (E j)

theorem extendScalar_pair (hΩ : MeasurableSet Ω) (f : Space → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (u : L2Scalar Ω) :
    WeakCurl.testPair f hf hc (extendScalar Ω hΩ u) = testPair Ω f hf hc u := by
  rw [WeakCurl.testPair_integral, testPair_integral]
  calc
    (∫ x, extendScalar Ω hΩ u x * f x) =
        ∫ x, Ω.indicator (fun y => u y * f y) x := by
      apply integral_congr_ae
      filter_upwards [extendScalar_ae Ω hΩ u] with x hx
      rw [hx]
      by_cases hm : x ∈ Ω <;> simp [hm]
    _ = ∫ x in Ω, u x * f x := integral_indicator hΩ

/-- After an interior cutoff, zero extension has precisely the product-rule curl.
No zero boundary condition on the original field is assumed. -/
theorem weakCurl_cutoff_extend (hΩ : IsOpen Ω) (χ : Test Ω)
    {E C : L2Vector Ω} (h : HasWeakCurl Ω E C) :
    WeakCurl.HasWeakCurl
      (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E))
      (extendVector Ω hΩ.measurableSet (productCurl Ω χ.toTest E C)) := by
  intro φ j
  have hh := h (outerProductTest Ω χ φ) j
  change weakCurl Ω (outerProductTest Ω χ φ) j E -
    valuePair Ω (outerProductTest Ω χ φ) (C j) = 0 at hh
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, derivativePair, valuePair, outerProductTest] at hh
  rw [derivative_pairing_product Ω χ.toTest φ,
    derivative_pairing_product Ω χ.toTest φ] at hh
  rw [← testPair_mulL2 Ω χ.function φ.function χ.regular.continuous χ.compact
    φ.regular.continuous φ.compact] at hh
  change WeakCurl.weakCurl φ j
      (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E)) -
    WeakCurl.valuePair φ
      (extendVector Ω hΩ.measurableSet (productCurl Ω χ.toTest E C) j) = 0
  simp only [WeakCurl.weakCurl, WeakCurl.derivativePair, WeakCurl.valuePair,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, extendVector, extendScalar_pair,
    productCurl, map_sub, map_add, multiply]
  linear_combination hh

end OQ14.CurlCutoff

#print axioms OQ14.CurlCutoff.multiplier_memLp
#print axioms OQ14.CurlCutoff.mulL2_ae
#print axioms OQ14.CurlCutoff.mulL2_norm_le
#print axioms OQ14.CurlCutoff.testPair_mulL2
#print axioms OQ14.CurlCutoff.derivativePair_product
#print axioms OQ14.CurlCutoff.weakCurl_multiply
#print axioms OQ14.CurlCutoff.cutoff_norm_le
#print axioms OQ14.CurlCutoff.extendScalar_ae
#print axioms OQ14.CurlCutoff.extendScalar_norm
#print axioms OQ14.CurlCutoff.extendScalar_pair
#print axioms OQ14.CurlCutoff.weakCurl_cutoff_extend

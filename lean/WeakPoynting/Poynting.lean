import WeakPoynting.Green

/-!
# Complex Poynting identity for actual weak H(curl) fields

Conjugation preserves the genuine distributional curl graph. The complex
Poynting law is deduced from the proved weak local Green identity.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.WeakPower

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakGreen
open scoped ComplexConjugate Topology

def conjScalar (u : L2Scalar) : L2Scalar :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).compLp u

theorem conjScalar_ae (u : L2Scalar) :
    (fun x => conjScalar u x) =ᵐ[volume] (fun x => conj (u x)) :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLp u

def conjVector (E : L2Vector) : L2Vector := fun j => conjScalar (E j)

def conjTest (φ : Test) : Test where
  function := fun x => conj (φ.function x)
  regular := Complex.conjCLE.contDiff.comp φ.regular
  compact := φ.compact.comp_left (map_zero (starRingEnd ℂ))

theorem valuePair_conj (φ : Test) (u : L2Scalar) :
    valuePair φ (conjScalar u) = conj (valuePair (conjTest φ) u) := by
  simp only [valuePair, testPair_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjScalar_ae u] with x hx
  simp [hx, conjTest]

theorem derivativePair_conj (φ : Test) (u : L2Scalar) (i : Fin 3) :
    derivativePair φ i (conjScalar u) = conj (derivativePair (conjTest φ) i u) := by
  simp only [derivativePair, testPair_integral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjScalar_ae u] with x hx
  dsimp only [conjTest]
  rw [partial_conj (φ.regular.differentiable (by norm_num) x)]
  simp [hx]

theorem hasWeakCurl_conjugate {E C : L2Vector} (h : HasWeakCurl E C) :
    HasWeakCurl (conjVector E) (conjVector C) := by
  intro φ j
  have hh := congrArg (starRingEnd ℂ) (h (conjTest φ) j)
  change conj (weakCurl (conjTest φ) j E - valuePair (conjTest φ) (C j)) = conj 0 at hh
  change weakCurl φ j (conjVector E) - valuePair φ (conjVector C j) = 0
  simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, conjVector, derivativePair_conj, valuePair_conj]
  simpa only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, map_sub, map_zero] using hh

def conjHCurl (u : HCurl) : HCurl :=
  ⟨(conjVector u.val.1, conjVector u.val.2), hasWeakCurl_conjugate u.property⟩

theorem weighted_product_integrable (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u v : L2Scalar) :
    Integrable (fun x => f x * u x * v x) := by
  apply (scalarProduct_integrable (scaleL2 f hf hc u) v).congr
  filter_upwards [scaleL2_ae f hf hc u] with x hx
  rw [hx]

theorem weighted_conjugate_integrable (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (u v : L2Scalar) :
    Integrable (fun x => f x * u x * conj (v x)) := by
  apply (weighted_product_integrable f hf hc u (conjScalar v)).congr
  filter_upwards [conjScalar_ae v] with x hx
  rw [hx]

theorem integral_weighted_conjugate (f : Space → ℂ) (u v : L2Scalar) :
    (∫ x, f x * u x * conjScalar v x) = ∫ x, f x * u x * conj (v x) := by
  apply integral_congr_ae
  filter_upwards [conjScalar_ae v] with x hx
  rw [hx]

/-- The actual distributional complex Poynting density tested against χ. -/
def poyntingDensity (χ : Test) (E C H K : L2Vector) (x : Space) : ℂ :=
  χ.function x * (dot (fun j => C j x) (conjugate (fun j => H j x)) -
    dot (fun j => E j x) (conjugate (fun j => K j x))) +
  dot (fun j => dcoord χ.function x j)
    (crossProduct (fun j => E j x) (conjugate (fun j => H j x)))

theorem poyntingDensity_integrable (χ : Test) (E C H K : L2Vector) :
    Integrable (poyntingDensity χ E C H K) := by
  have hi (u v : L2Scalar) := weighted_conjugate_integrable χ.function
    χ.regular.continuous χ.compact u v
  have hd (i : Fin 3) (u v : L2Scalar) := weighted_conjugate_integrable
    (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
    (χ.compact.fderiv_apply ℝ (basis i)) u v
  have hsum := ((((hi (C 0) (H 0)).add (hi (C 1) (H 1))).add (hi (C 2) (H 2))).sub
    (((hi (E 0) (K 0)).add (hi (E 1) (K 1))).add (hi (E 2) (K 2)))).add
    ((((hd 0 (E 1) (H 2)).sub (hd 0 (E 2) (H 1))).add
      ((hd 1 (E 2) (H 0)).sub (hd 1 (E 0) (H 2)))).add
      ((hd 2 (E 0) (H 1)).sub (hd 2 (E 1) (H 0))))
  convert hsum using 1
  ext x
  simp only [poyntingDensity, dot, conjugate, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Pi.add_apply, Pi.sub_apply]
  ring

theorem poyntingDensity_integral (χ : Test) (E C H K : L2Vector) :
    (∫ x, poyntingDensity χ E C H K x) =
      localGreenIntegral χ E C (conjVector H) (conjVector K) := by
  have hi (u v : L2Scalar) := weighted_conjugate_integrable χ.function
    χ.regular.continuous χ.compact u v
  have hd (i : Fin 3) (u v : L2Scalar) := weighted_conjugate_integrable
    (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
    (χ.compact.fderiv_apply ℝ (basis i)) u v
  have heq : poyntingDensity χ E C H K = fun x =>
      χ.function x * C 0 x * conj (H 0 x) + χ.function x * C 1 x * conj (H 1 x) +
      χ.function x * C 2 x * conj (H 2 x) +
      dcoord χ.function x 1 * E 2 x * conj (H 0 x) -
      dcoord χ.function x 2 * E 1 x * conj (H 0 x) +
      dcoord χ.function x 2 * E 0 x * conj (H 1 x) -
      dcoord χ.function x 0 * E 2 x * conj (H 1 x) +
      dcoord χ.function x 0 * E 1 x * conj (H 2 x) -
      dcoord χ.function x 1 * E 0 x * conj (H 2 x) -
      (χ.function x * E 0 x * conj (K 0 x) + χ.function x * E 1 x * conj (K 1 x) +
       χ.function x * E 2 x * conj (K 2 x)) := by
    funext x
    simp only [poyntingDensity, dot, conjugate, cross_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [heq]
  simp only [localGreenIntegral, conjVector, integral_weighted_conjugate]
  have h0 := ((hi (C 0) (H 0)).add (hi (C 1) (H 1))).add (hi (C 2) (H 2))
  have h1 := h0.add (hd 1 (E 2) (H 0))
  have h2 := h1.sub (hd 2 (E 1) (H 0))
  have h3 := h2.add (hd 2 (E 0) (H 1))
  have h4 := h3.sub (hd 0 (E 2) (H 1))
  have h5 := h4.add (hd 0 (E 1) (H 2))
  have h6 := h5.sub (hd 1 (E 0) (H 2))
  have hK := ((hi (E 0) (K 0)).add (hi (E 1) (K 1))).add (hi (E 2) (K 2))
  have hC01 := (hi (C 0) (H 0)).add (hi (C 1) (H 1))
  have hK01 := (hi (E 0) (K 0)).add (hi (E 1) (K 1))
  dsimp only [Pi.add_def, Pi.sub_def] at h0 h1 h2 h3 h4 h5 h6 hK hC01 hK01
  rw [integral_sub h6 hK,
    integral_sub h5 (hd 1 (E 0) (H 2)), integral_add h4 (hd 0 (E 1) (H 2)),
    integral_sub h3 (hd 0 (E 2) (H 1)), integral_add h2 (hd 2 (E 0) (H 1)),
    integral_sub h1 (hd 2 (E 1) (H 0)), integral_add h0 (hd 1 (E 2) (H 0)),
    integral_add hC01 (hi (C 2) (H 2)),
    integral_add (hi (C 0) (H 0)) (hi (C 1) (H 1)),
    integral_add hK01 (hi (E 2) (K 2)),
    integral_add (hi (E 0) (K 0)) (hi (E 1) (K 1))]

/-- The complex Poynting identity for arbitrary weak H(curl) fields;
no pointwise differentiability of either field is required. -/
theorem weak_complex_Poynting (χ : Test) (E H : HCurl) :
    (∫ x, poyntingDensity χ E.val.1 E.val.2 H.val.1 H.val.2 x) = 0 := by
  rw [poyntingDensity_integral]
  exact weak_local_Green χ E (conjHCurl H)

end OQ14.WeakPower

#print axioms OQ14.WeakPower.hasWeakCurl_conjugate
#print axioms OQ14.WeakPower.weighted_conjugate_integrable
#print axioms OQ14.WeakPower.poyntingDensity_integrable
#print axioms OQ14.WeakPower.poyntingDensity_integral
#print axioms OQ14.WeakPower.weak_complex_Poynting

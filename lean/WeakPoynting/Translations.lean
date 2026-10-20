import WeakPoynting.PartialSmoothing

/-! # Quantitative translation estimates from actual weak L2 derivatives -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.WeakTranslations

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.WeakGreen OQ14.WeakPower Filter
open scoped Topology SchwartzMap ComplexConjugate InnerProductSpace

theorem scalarProduct_norm_le (u v : L2Scalar) :
    ‖scalarProduct u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [scalarProduct_integral]
  exact (norm_integral_le_integral_norm _).trans
    (by simpa only [norm_mul] using integral_norm_mul_le u v)

theorem valuePair_norm_le (φ : Test) (u : L2Scalar) :
    ‖valuePair φ u‖ ≤ ‖u‖ * ‖testL2 φ‖ := by
  rw [show valuePair φ u = scalarProduct u (testL2 φ) from
    (scalarProduct_continuousL2 u φ.function φ.regular.continuous φ.compact).symm]
  exact scalarProduct_norm_le u (testL2 φ)

theorem shifted_test_norm (φ : Test) (a : Space) :
    ‖testL2 (shiftedTest φ a)‖ = ‖testL2 φ‖ := by
  simp only [testL2, continuousL2, Lp.norm_toLp]
  congr 1
  exact eLpNorm_comp_measurePreserving φ.regular.continuous.aestronglyMeasurable
    (Measure.measurePreserving_sub_left volume a)

theorem smoothScalar_norm_le (φ : Test) (u : L2Scalar) (a : Space) :
    ‖smoothScalar φ.function u a‖ ≤ ‖u‖ * ‖testL2 φ‖ := by
  have he : smoothScalar φ.function u a = valuePair (shiftedTest φ a) u := by
    rw [valuePair, testPair_integral]
    rfl
  rw [he, ← shifted_test_norm φ a]
  exact valuePair_norm_le (shiftedTest φ a) u

theorem basis_expansion (v : Space) : v = ∑ i : Fin 3, v i • basis i := by
  ext j
  fin_cases j <;> simp [Fin.sum_univ_three, basis, EuclideanSpace.single_apply]

theorem coordinate_opNorm_le (L : Space →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (basis i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro v
  calc
    ‖L v‖ = ‖∑ i : Fin 3, v i • L (basis i)‖ := by
      conv_lhs => rw [basis_expansion v, map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • L (basis i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖L (basis i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (basis i)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

theorem smoothScalar_difference_bound (φ : Test) {u : L2Scalar} {D : Fin 3 → L2Scalar}
    (hD : ∀ i, HasWeakPartial u (D i) i) (a : Space) :
    ‖smoothScalar φ.function u a - smoothScalar φ.function u 0‖ ≤
      ((∑ i, ‖D i‖) * ‖testL2 φ‖) * ‖a‖ := by
  have hd (x : Space) : ‖fderiv ℝ (smoothScalar φ.function u) x‖ ≤
      (∑ i, ‖D i‖) * ‖testL2 φ‖ := by
    apply (coordinate_opNorm_le _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    change ‖dcoord (smoothScalar φ.function u) x i‖ ≤ _
    rw [smoothScalar_weakPartial φ (hD i)]
    exact smoothScalar_norm_le φ (D i) x
  simpa only [sub_zero] using
    (convex_univ : Convex ℝ (Set.univ : Set Space)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => (smoothScalar_regular φ.regular φ.compact u).differentiable le_rfl x)
      (fun x _ => hd x) (Set.mem_univ (0 : Space)) (Set.mem_univ a)

theorem valuePair_translate (φ : Test) (u : L2Scalar) (a : Space) :
    valuePair φ (translateL2 u a) = smoothScalar (shiftedTest φ 0).function u a := by
  rw [valuePair, testPair_integral, smoothScalar_integral]
  calc
    (∫ x, translateL2 u a x * φ.function x) = ∫ x, u (x + a) * φ.function x := by
      apply integral_congr_ae
      filter_upwards [translateL2_ae u a] with x hx
      rw [hx]
    _ = ∫ x, u x * φ.function (x - a) := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun x => u x * φ.function (x - a)) a
    _ = _ := by simp only [shiftedTest, zero_sub, neg_sub]

theorem translated_test_bound (φ : Test) {u : L2Scalar} {D : Fin 3 → L2Scalar}
    (hD : ∀ i, HasWeakPartial u (D i) i) (a : Space) :
    ‖valuePair φ (translateL2 u a - u)‖ ≤
      (‖a‖ * ∑ i, ‖D i‖) * ‖testL2 φ‖ := by
  have h := smoothScalar_difference_bound (shiftedTest φ 0) hD a
  rw [shifted_test_norm] at h
  rw [map_sub, valuePair_translate, show valuePair φ u =
      smoothScalar (shiftedTest φ 0).function u 0 from by
        rw [← valuePair_translate, translateL2_zero]]
  nlinarith [h]

theorem translate_compact {u : L2Scalar} (hu : CompactRepresentative u) (a : Space) :
    CompactRepresentative (translateL2 u a) := by
  obtain ⟨f, hc, he⟩ := hu
  refine ⟨fun x => f (x + a), hc.comp_homeomorph (Homeomorph.addRight a), ?_⟩
  have hh := (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae.eventually he
  filter_upwards [translateL2_ae u a, hh] with x hx hy
  exact hx.trans hy

theorem compact_sub {u v : L2Scalar} (hu : CompactRepresentative u)
    (hv : CompactRepresentative v) : CompactRepresentative (u - v) := by
  obtain ⟨f, hf, he⟩ := hu
  obtain ⟨g, hg, hge⟩ := hv
  refine ⟨fun x => f x - g x, ?_, ?_⟩
  · simpa only [sub_eq_add_neg] using hf.add (hg.comp_left (g := fun z : ℂ => -z) neg_zero)
  filter_upwards [Lp.coeFn_sub u v, he, hge] with x hx hu hv
  simpa only [Pi.sub_apply, hu, hv] using hx

theorem conjugate_test_norm (φ : Test) : ‖testL2 (conjTest φ)‖ = ‖testL2 φ‖ := by
  simp only [testL2, continuousL2, Lp.norm_toLp, conjTest]
  congr 1
  exact eLpNorm_conj φ.function 2 volume

theorem valuePair_conjugate_inner (φ : Test) (u : L2Scalar) :
    valuePair (conjTest φ) u = ⟪testL2 φ, u⟫_ℂ := by
  rw [valuePair, testPair_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2_ae φ.function φ.regular.continuous φ.compact] with x hx
  change u x * conj (φ.function x) = inner (𝕜 := ℂ) (testL2 φ x) (u x)
  rw [show testL2 φ x = φ.function x from hx]
  simp [RCLike.inner_apply, mul_comm]

def smoothedTest (φ : ContDiffBump (0 : Space)) (u : L2Scalar)
    (hu : CompactRepresentative u) : Test where
  function := smoothScalar (complexKernel φ) u
  regular := (smoothScalar_regular (complexKernel_regular φ) (complexKernel_compact φ) u).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  compact := smoothScalar_compact _ (complexKernel_compact φ) u hu

theorem smoothedTest_L2 (φ : ContDiffBump (0 : Space)) (u : L2Scalar)
    (hu : CompactRepresentative u) : testL2 (smoothedTest φ u hu) = mollifyL2 φ u := by
  apply Lp.ext
  exact (continuousL2_ae _ (smoothedTest φ u hu).regular.continuous
    (smoothedTest φ u hu).compact).trans (smoothScalar_memLp φ u).coeFn_toLp.symm

/-- Dual norm control is proved using the explicit compact mollifications of
the field itself, so no density assumption is hidden in this criterion. -/
theorem norm_le_of_compact_test_bound (u : L2Scalar) (hu : CompactRepresentative u)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ φ : Test, ‖valuePair φ u‖ ≤ B * ‖testL2 φ‖) :
    ‖u‖ ≤ B := by
  have hb (n : ℕ) : ‖⟪mollifyL2 (shrinkingBump n) u, u⟫_ℂ‖ ≤ B * ‖u‖ := by
    have hh := h (conjTest (smoothedTest (shrinkingBump n) u hu))
    rw [valuePair_conjugate_inner, conjugate_test_norm, smoothedTest_L2] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (by rw [mollifyL2_eq_average]; exact averageL2_norm_le _ u) hB)
  have ht : Tendsto (fun n => ‖⟪mollifyL2 (shrinkingBump n) u, u⟫_ℂ‖)
      atTop (𝓝 ‖⟪u, u⟫_ℂ‖) :=
    ((mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto u).inner tendsto_const_nhds).norm
  have hn := le_of_tendsto ht (Eventually.of_forall hb)
  rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hn
  nlinarith [norm_nonneg u]

/-- Quantitative L2 translation continuity derived from actual weak derivatives. -/
theorem weak_translation_bound {u : L2Scalar} (hu : CompactRepresentative u)
    {D : Fin 3 → L2Scalar} (hD : ∀ i, HasWeakPartial u (D i) i) (a : Space) :
    ‖translateL2 u a - u‖ ≤ ‖a‖ * ∑ i, ‖D i‖ := by
  apply norm_le_of_compact_test_bound _ (compact_sub (translate_compact hu a) hu) (by positivity)
  intro φ
  exact translated_test_bound φ hD a

/-- The actual smooth convolution approximates uniformly on a weak derivative ball. -/
theorem weak_mollification_bound (φ : ContDiffBump (0 : Space)) {u : L2Scalar}
    (hu : CompactRepresentative u) {D : Fin 3 → L2Scalar}
    (hD : ∀ i, HasWeakPartial u (D i) i) :
    ‖mollifyL2 φ u - u‖ ≤ φ.rOut * ∑ i, ‖D i‖ := by
  have hh := φ.dist_normed_convolution_le (μ := (volume : Measure Space))
    (translateL2_continuous u).aestronglyMeasurable
    (x₀ := (0 : Space)) (ε := φ.rOut * ∑ i, ‖D i‖) (by
      intro a ha
      rw [translateL2_zero, dist_eq_norm]
      apply (weak_translation_bound hu hD a).trans
      exact mul_le_mul_of_nonneg_right
        (by exact (show ‖a‖ < φ.rOut from by simpa only [Metric.mem_ball, dist_zero_right] using ha).le)
        (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  simpa only [averageL2, translateL2_zero, dist_eq_norm, mollifyL2_eq_average] using hh

end OQ14.WeakTranslations

#print axioms OQ14.WeakTranslations.smoothScalar_difference_bound
#print axioms OQ14.WeakTranslations.valuePair_translate
#print axioms OQ14.WeakTranslations.translated_test_bound
#print axioms OQ14.WeakTranslations.translate_compact
#print axioms OQ14.WeakTranslations.norm_le_of_compact_test_bound
#print axioms OQ14.WeakTranslations.weak_translation_bound
#print axioms OQ14.WeakTranslations.weak_mollification_bound

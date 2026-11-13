import WeakPoynting.Translations
import MaxwellDifferenceQuotient

/-! A single genuine weak partial controls difference quotients in that
coordinate direction; no normal or other tangential derivative is needed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DirectionalQuotient
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurlCompact
  OQ14.PartialSmoothing OQ14.WeakTranslations OQ14.MaxwellDifferenceQuotient

theorem directional_smooth_difference (φ : Test) (u D : L2Scalar) (i : Fin 3)
    (hD : HasWeakPartial u D i) (h : ℝ) :
    ‖smoothScalar φ.function u (h • basis i) - smoothScalar φ.function u 0‖ ≤
      |h| * ‖D‖ * ‖testL2 φ‖ := by
  let f : ℝ → ℂ := fun t => smoothScalar φ.function u (t • basis i)
  have hd (t : ℝ) : HasDerivAt f (smoothScalar φ.function D (t • basis i)) t := by
    have hcomp := ((smoothScalar_regular φ.regular φ.compact u).differentiable le_rfl (t • basis i)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const (basis i))
    simp only [id_eq, one_smul, Function.comp_def] at hcomp
    change HasDerivAt f (fderiv ℝ (smoothScalar φ.function u) (t • basis i) (basis i)) t at hcomp
    rw [show fderiv ℝ (smoothScalar φ.function u) (t • basis i) (basis i) =
      smoothScalar φ.function D (t • basis i) from smoothScalar_weakPartial φ hD _] at hcomp
    exact hcomp
  have hb (t : ℝ) : ‖deriv f t‖ ≤ ‖D‖ * ‖testL2 φ‖ := by
    rw [(hd t).deriv]
    exact smoothScalar_norm_le φ D (t • basis i)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hd t).differentiableAt) (fun t _ => hb t) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ h)
  simpa [f, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using hm

theorem directional_translated_test_bound (φ : Test) (u D : L2Scalar) (i : Fin 3)
    (hD : HasWeakPartial u D i) (h : ℝ) :
    ‖valuePair φ (translateL2 u (h • basis i) - u)‖ ≤
      (|h| * ‖D‖) * ‖testL2 φ‖ := by
  have ht := directional_smooth_difference (shiftedTest φ 0) u D i hD h
  rw [shifted_test_norm] at ht
  rw [map_sub, valuePair_translate, show valuePair φ u =
      smoothScalar (shiftedTest φ 0).function u 0 from by
        rw [← valuePair_translate, translateL2_zero]]
  exact ht

theorem directional_quotient_bound (u D : L2Scalar) (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) (h : ℝ) (hh : h ≠ 0) :
    ‖quotient u i h‖ ≤ ‖D‖ := by
  have ht : ‖translateL2 u (h • basis i) - u‖ ≤ |h| * ‖D‖ := by
    apply norm_le_of_compact_test_bound _ (compact_sub (translate_compact hu _) hu) (by positivity)
    intro φ
    exact directional_translated_test_bound φ u D i hD h
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  unfold quotient
  rw [norm_smul, norm_inv, Complex.norm_real]
  apply (inv_mul_le_iff₀ hn).2
  simpa only [Real.norm_eq_abs, mul_comm] using ht

end OQ14.Packet05DirectionalQuotient
#print axioms OQ14.Packet05DirectionalQuotient.directional_smooth_difference
#print axioms OQ14.Packet05DirectionalQuotient.directional_translated_test_bound
#print axioms OQ14.Packet05DirectionalQuotient.directional_quotient_bound

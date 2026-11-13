import Packet05ScalarDifferenceDivergence

/-! Translation and differences commute with actual weak partial derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarDifferencePartial
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.DivCurlCompact
  OQ14.MaxwellDifferenceQuotient

theorem translate_weak_partial (u v : L2Scalar) (i : Fin 3)
    (hu : HasWeakPartial u v i) (a : Space) :
    HasWeakPartial (translateL2 u a) (translateL2 v a) i := by
  intro φ
  have ht := hu (shifted φ a)
  simp only [valuePair, derivativePair, testPair_integral, shifted_value, shifted_partial] at ht ⊢
  simpa only [translated_integral] using ht

theorem quotient_weak_partial (u v : L2Scalar) (i j : Fin 3)
    (hu : HasWeakPartial u v i) (h : ℝ) :
    HasWeakPartial (quotient u j h) (quotient v j h) i := by
  intro φ
  have ht := translate_weak_partial u v i hu (h • basis j) φ
  have hv := hu φ
  change valuePair φ (((h : ℂ)⁻¹) • (translateL2 v (h • basis j) - v)) +
    derivativePair φ i (((h : ℂ)⁻¹) • (translateL2 u (h • basis j) - u)) = 0
  simp only [map_smul, map_sub, smul_eq_mul]
  linear_combination (h : ℂ)⁻¹ * ht - (h : ℂ)⁻¹ * hv

end OQ14.Packet05ScalarDifferencePartial
#print axioms OQ14.Packet05ScalarDifferencePartial.translate_weak_partial
#print axioms OQ14.Packet05ScalarDifferencePartial.quotient_weak_partial

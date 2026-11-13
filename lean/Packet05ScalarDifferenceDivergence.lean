import Packet05DivergenceUpgrade
import Packet05ScalarTransmissionFlux

/-! Difference quotients preserve the actual distributional divergence
identity, with the translated smooth test used explicitly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarDifferenceDivergence
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.DivCurlCompact
  OQ14.MaxwellDifferenceQuotient

theorem translate_weak_divergence (E : L2Vector) (D : L2Scalar)
    (h : HasWeakDivergence E D) (a : Space) :
    HasWeakDivergence (translateVector E a) (translateL2 D a) := by
  apply (hasWeakDivergence_integral _ _).mpr
  intro φ
  have ht := (hasWeakDivergence_integral E D).mp h (shifted φ a)
  simp only [shifted_value, shifted_partial] at ht
  simpa only [translateVector, translated_integral] using ht

theorem quotient_weak_divergence (E : L2Vector) (D : L2Scalar)
    (hdiv : HasWeakDivergence E D) (i : Fin 3) (h : ℝ) :
    HasWeakDivergence (quotientVector E i h) (quotient D i h) := by
  intro φ
  have ht := translate_weak_divergence E D hdiv (h • basis i) φ
  have hu := hdiv φ
  change valuePair φ (((h : ℂ)⁻¹) • (translateL2 D (h • basis i) - D)) +
    derivativePair φ 0 (((h : ℂ)⁻¹) • (translateL2 (E 0) (h • basis i) - E 0)) +
    derivativePair φ 1 (((h : ℂ)⁻¹) • (translateL2 (E 1) (h • basis i) - E 1)) +
    derivativePair φ 2 (((h : ℂ)⁻¹) • (translateL2 (E 2) (h • basis i) - E 2)) = 0
  simp only [map_smul, map_sub, smul_eq_mul]
  change valuePair φ (translateL2 D (h • basis i)) +
    derivativePair φ 0 (translateL2 (E 0) (h • basis i)) +
    derivativePair φ 1 (translateL2 (E 1) (h • basis i)) +
    derivativePair φ 2 (translateL2 (E 2) (h • basis i)) = 0 at ht
  linear_combination (h : ℂ)⁻¹ * ht - (h : ℂ)⁻¹ * hu

end OQ14.Packet05ScalarDifferenceDivergence
#print axioms OQ14.Packet05ScalarDifferenceDivergence.translate_weak_divergence
#print axioms OQ14.Packet05ScalarDifferenceDivergence.quotient_weak_divergence

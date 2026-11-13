import Packet06ComplexAffine
import DilationReciprocity
import Packet06PhysicalScale

/-! Exact scaling of the physical reciprocal normalization at complex frequency. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06ComplexReciprocal
open OQ14.Packet06PhysicalNormalization OQ14.DilationReciprocity

theorem reciprocalNorm_dilate (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2) :
    reciprocalNorm (FrequencyScalingMaxwell.scaleCoeff s c) (R/s) ((s : ℂ)*z) (DilationL2.dilate s u) =
      (s : ℂ)⁻¹ * reciprocalNorm c R z u := by
  rw [reciprocalNorm_eq_crossing _ _ (div_nonneg hR hs.le), reciprocalNorm_eq_crossing c R hR,
    derivative_pairing_scale s R hs hR]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  field_simp
  ring

theorem reciprocalNorm_dilate_rescale (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z a : ℂ) (u : VectorFourier.VectorL2) :
    reciprocalNorm (FrequencyScalingMaxwell.scaleCoeff s c) (R/s) ((s : ℂ)*z) (a • DilationL2.dilate s u) =
      a^2 * (s : ℂ)⁻¹ * reciprocalNorm c R z u := by
  rw [Packet06PhysicalScale.reciprocalNorm_scale _ _ (div_nonneg hR hs.le), reciprocalNorm_dilate s R hs hR]
  ring

end OQ14.Packet06ComplexReciprocal
#print axioms OQ14.Packet06ComplexReciprocal.reciprocalNorm_dilate
#print axioms OQ14.Packet06ComplexReciprocal.reciprocalNorm_dilate_rescale

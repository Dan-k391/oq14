import Packet05LocalizedForcingNorm
import Packet05ScalarCutoffTransfer

/-! Uniform norms of the actual outer-cutoff scalar and forcing fields. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05RegionalLocalizedNorm
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05TensorCommutator OQ14.Packet05FlatWeight
  OQ14.Packet05ScalarVectorBounds OQ14.Packet05LocalizedForcingNorm

theorem localized_fields_norm (κ : RealTest univ) (A : Fin 3 → Fin 3 → Test)
    (u : L2Scalar) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (U P F0 a α β : ℝ) (hU : ‖u‖ ≤ U) (hP : ∀ j, ‖C j‖ ≤ P) (hF : ∀ j, ‖F j‖ ≤ F0)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hα : ∀ x, ‖κ.complexTest.function x‖ ≤ α) (hβ : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ β) :
    ‖cutScalar κ u‖ ≤ α*U ∧
    (∀ j, ‖localizedGradient κ u C j‖ ≤ α*P+β*U) ∧
    (∀ j, ‖localizedForcing κ A u F d hd j‖ ≤ α*F0+3*(1+d)*a*β*U) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hd0 : 0 ≤ 1+d := by linarith
  constructor
  · have h := OQ14.InteriorTestDensity.scaleL2_norm_le κ.complexTest.function κ.complexTest.regular.continuous κ.complexTest.compact u hα
    exact h.trans (mul_le_mul_of_nonneg_left hU hα0)
  constructor
  · intro j
    have h := localized_gradient_norm κ u C α β hα hβ j
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left (hP j) hα0)
      (mul_le_mul_of_nonneg_left hU hβ0))
  · intro j
    have hf := OQ14.InteriorTestDensity.scaleL2_norm_le κ.complexTest.function κ.complexTest.regular.continuous κ.complexTest.compact (F j) hα
    have hq (k : Fin 3) : ‖cutoffCorrection κ u k‖ ≤ β*‖u‖ :=
      OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord κ.complexTest.function x k)
        (partial_continuous κ.complexTest.regular k) (κ.complexTest.compact.fderiv_apply ℝ (basis k)) u (hβ k)
    have hsum : ‖cutoffCorrection κ u 0‖+‖cutoffCorrection κ u 1‖+‖cutoffCorrection κ u 2‖ ≤ 3*β*‖u‖ := by linarith [hq 0,hq 1,hq 2]
    have hm := matrixField_norm A (cutoffCorrection κ u) j a (ha j)
    have hw := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd (matrixField A (cutoffCorrection κ u) j)
    have hms := mul_le_mul_of_nonneg_left hsum ha0
    have hbound : ‖matrixField A (cutoffCorrection κ u) j‖ ≤ 3*a*β*‖u‖ := by nlinarith
    have hw' := mul_le_mul_of_nonneg_left hbound hd0
    have hfu := mul_le_mul_of_nonneg_left (hF j) hα0
    have huu := mul_le_mul_of_nonneg_left hU (show 0 ≤ 3*(1+d)*a*β by positivity)
    change ‖scaleL2 κ.complexTest.function κ.complexTest.regular.continuous κ.complexTest.compact (F j) +
      mulWeight d hd (matrixField A (cutoffCorrection κ u) j)‖ ≤ _
    exact (norm_add_le _ _).trans (by nlinarith)

end OQ14.Packet05RegionalLocalizedNorm
#print axioms OQ14.Packet05RegionalLocalizedNorm.localized_fields_norm

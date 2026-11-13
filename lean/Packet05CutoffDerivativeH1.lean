import Packet05CurlSourceH1

/-! Differentiating a localized weak derivative once more keeps both the
cutoff-gradient term and its derivative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffDerivativeH1
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05PartialProduct OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1

theorem cutoff_product_derivative_partial (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (u Ui Ut Uit : L2Scalar) (i t : Fin 3)
    (hUi : HasWeakPartial Ui Uit t) (hUt : HasWeakPartial u Ut t) :
    HasWeakPartial (cutoffProductDerivative χ u Ui i)
      (cutoffProductDerivative χ Ui Uit t +
        cutoffProductDerivative (derivativeCutoff χ hχ i) u Ut t) t := by
  have h1 := cutoff_weak_partial χ Ui Uit t hUi
  have h2 := cutoff_weak_partial (derivativeCutoff χ hχ i) u Ut t hUt
  intro φ
  have h1 := h1 φ
  have h2 := h2 φ
  simp only [cutoffProductDerivative, derivativeCutoff, map_add] at h1 h2 ⊢
  linear_combination h1+h2

end OQ14.Packet05CutoffDerivativeH1
#print axioms OQ14.Packet05CutoffDerivativeH1.cutoff_product_derivative_partial

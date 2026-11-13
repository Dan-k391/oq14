import Packet05LocalSecondTangential
import Packet05CutoffDerivativeH1

/-! Interior mixed weak derivatives become genuine global mixed derivatives
after a smooth cutoff, including both cutoff product terms. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05LocalCutoffMixed
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct OQ14.Packet05CurlSourceH1
  OQ14.MaxwellCutoffCommutator

theorem local_cutoff_mixed (V : Set Space) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχV : tsupport χ.function ⊆ V) (u Ui Ut Uit : L2Scalar) (i t : Fin 3)
    (hUi : HasPartialOn V Ui Uit t) (hUt : HasPartialOn V u Ut t) :
    HasWeakPartial (cutoffProductDerivative χ u Ui i)
      (cutoffProductDerivative χ Ui Uit t +
        cutoffProductDerivative (derivativeCutoff χ hχ2 i) u Ut t) t := by
  have hdV : tsupport (derivativeCutoff χ hχ2 i).function ⊆ V :=
    (RegionalMaxwellHelmholtz.partial_tsupport χ.function i).trans hχV
  have h1 := local_cutoff_weak_partial V χ hχV Ui Uit t hUi
  have h2 := local_cutoff_weak_partial V (derivativeCutoff χ hχ2 i) hdV u Ut t hUt
  intro φ
  have h1 := h1 φ
  have h2 := h2 φ
  simp only [cutoffProductDerivative, derivativeCutoff, map_add] at h1 h2 ⊢
  linear_combination h1+h2

end OQ14.Packet05LocalCutoffMixed
#print axioms OQ14.Packet05LocalCutoffMixed.local_cutoff_mixed

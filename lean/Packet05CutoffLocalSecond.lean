import Packet05ActualLocalSecondDerivatives
import Packet05LocalCutoffMixed

/-! Promote actual local tangential derivatives to global derivatives of an
inner cutoff, with the cutoff derivatives kept explicitly. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffLocalSecond
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct
  OQ14.Packet05LocalCutoffMixed OQ14.Packet05CurlSourceH1 OQ14.MaxwellCutoffCommutator

theorem cutoff_local_second (V : Set Space) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχV : tsupport χ.function ⊆ V) (u Di Dt Dit : L2Scalar) (i t : Fin 3)
    (hi : HasPartialOn V u Di i) (ht : HasPartialOn V u Dt t)
    (hit : HasPartialOn V Di Dit t) :
    HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact u)
      (cutoffProductDerivative χ u Di i) i ∧
    HasWeakPartial (cutoffProductDerivative χ u Di i)
      (cutoffProductDerivative χ Di Dit t +
        cutoffProductDerivative (derivativeCutoff χ hχ2 i) u Dt t) t := by
  exact ⟨local_cutoff_weak_partial V χ hχV u Di i hi,
    local_cutoff_mixed V χ hχ2 hχV u Di Dt Dit i t hit ht⟩

end OQ14.Packet05CutoffLocalSecond
#print axioms OQ14.Packet05CutoffLocalSecond.cutoff_local_second

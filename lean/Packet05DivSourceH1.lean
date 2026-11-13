import Packet05CurlSourceH1

/-! Weak H¹ stability of the divergence-cutoff commutator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DivSourceH1
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05PartialProduct
  OQ14.Packet05CurlSourceH1

def divergenceSource (χ : Test) (hχ : ContDiff ℝ 2 χ.function) (W : L2Vector) : L2Scalar :=
  ∑ j : Fin 3, scaleL2 (derivativeCutoff χ hχ j).function
    (derivativeCutoff χ hχ j).regular.continuous (derivativeCutoff χ hχ j).compact (W j)

def divergenceSourceDerivative (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W DW : L2Vector) (i : Fin 3) : L2Scalar :=
  ∑ j : Fin 3, cutoffProductDerivative (derivativeCutoff χ hχ j) (W j) (DW j) i

theorem divergence_source_weak_partial (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W DW : L2Vector) (i : Fin 3) (hW : ∀ j, HasWeakPartial (W j) (DW j) i) :
    HasWeakPartial (divergenceSource χ hχ W) (divergenceSourceDerivative χ hχ W DW i) i := by
  have h (j : Fin 3) := cutoff_weak_partial (derivativeCutoff χ hχ j) (W j) (DW j) i (hW j)
  intro φ
  have h0 := h 0 φ
  have h1 := h 1 φ
  have h2 := h 2 φ
  simp only [divergenceSource, divergenceSourceDerivative, Fin.sum_univ_three, map_add, cutoffProductDerivative]
  simp only [map_add] at h0 h1 h2
  linear_combination h0 + h1 + h2

end OQ14.Packet05DivSourceH1
#print axioms OQ14.Packet05DivSourceH1.divergence_source_weak_partial

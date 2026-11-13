import Packet05PartialProduct
import MaxwellCurlCutoffSource

/-! Weak H¹ stability of the actual curl-cutoff commutator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05CurlSourceH1
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.MaxwellCurlCutoffSource
  OQ14.Packet05PartialProduct

def cutoffProductDerivative (χ : Test) (u D : L2Scalar) (i : Fin 3) : L2Scalar :=
  scaleL2 χ.function χ.regular.continuous χ.compact D +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u

def curlSourceDerivative (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W DW : L2Vector) (i j : Fin 3) : L2Scalar :=
  cutoffProductDerivative (derivativeCutoff χ hχ (next j)) (W (previous j)) (DW (previous j)) i -
  cutoffProductDerivative (derivativeCutoff χ hχ (previous j)) (W (next j)) (DW (next j)) i

theorem curl_source_weak_partial (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W DW : L2Vector) (i j : Fin 3) (hW : ∀ k, HasWeakPartial (W k) (DW k) i) :
    HasWeakPartial (source χ hχ W j) (curlSourceDerivative χ hχ W DW i j) i := by
  have h1 := cutoff_weak_partial (derivativeCutoff χ hχ (next j))
    (W (previous j)) (DW (previous j)) i (hW (previous j))
  have h2 := cutoff_weak_partial (derivativeCutoff χ hχ (previous j))
    (W (next j)) (DW (next j)) i (hW (next j))
  intro φ
  have h1 := h1 φ
  have h2 := h2 φ
  change valuePair φ (_ - _) + derivativePair φ i (_ - _) = 0
  simp only [map_sub, cutoffProductDerivative]
  linear_combination h1 - h2

end OQ14.Packet05CurlSourceH1
#print axioms OQ14.Packet05CurlSourceH1.curl_source_weak_partial

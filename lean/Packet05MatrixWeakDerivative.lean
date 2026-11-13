import Packet05WeightTangentialDerivative
import Packet05PartialProduct
import Packet05TensorCommutator
import MaxwellCutoffCommutator

/-! Actual weak product rule for a smooth matrix times an H¹ vector field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05MatrixWeakDerivative
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05TensorCommutator OQ14.Packet05PartialProduct OQ14.MaxwellCutoffCommutator

def derivativeMatrix (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (i : Fin 3) : Fin 3 → Fin 3 → Test :=
  fun j k => derivativeCutoff (A j k) (hA j k) i

theorem matrix_weak_partial (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (C DC : L2Vector) (i j : Fin 3) (hC : ∀ k, HasWeakPartial (C k) (DC k) i) :
    HasWeakPartial (matrixField A C j)
      (matrixField A DC j + matrixField (derivativeMatrix A hA i) C j) i := by
  have h0 := cutoff_weak_partial (A j 0) (C 0) (DC 0) i (hC 0)
  have h1 := cutoff_weak_partial (A j 1) (C 1) (DC 1) i (hC 1)
  have h2 := cutoff_weak_partial (A j 2) (C 2) (DC 2) i (hC 2)
  intro φ
  have h0 := h0 φ
  have h1 := h1 φ
  have h2 := h2 φ
  simp only [matrixField, derivativeMatrix, derivativeCutoff, map_add] at h0 h1 h2 ⊢
  linear_combination h0 + h1 + h2

end OQ14.Packet05MatrixWeakDerivative
#print axioms OQ14.Packet05MatrixWeakDerivative.matrix_weak_partial

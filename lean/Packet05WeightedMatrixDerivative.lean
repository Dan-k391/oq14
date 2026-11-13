import Packet05MatrixWeakDerivative
import Packet05DirectionalWeightDerivative
import Packet05ScalarCutoffTesting
import WeakPoynting.Translations

/-! Compactness and tangential weak derivative of the actual binary-weighted
matrix flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05WeightedMatrixDerivative
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.WeakTranslations OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05DirectionalWeightDerivative OQ14.Packet05ScalarCutoffTesting

theorem compact_neg (u : L2Scalar) (hu : CompactRepresentative u) : CompactRepresentative (-u) := by
  obtain ⟨f,hf,he⟩ := hu
  have hneg : HasCompactSupport (-f) := by
    exact hf.comp_left (g := fun z : ℂ => -z) (by simp)
  refine ⟨-f,hneg,?_⟩
  filter_upwards [Lp.coeFn_neg u, he] with x hn hx
  rw [hn]
  simp only [Pi.neg_apply, hx]

theorem compact_add (u v : L2Scalar) (hu : CompactRepresentative u) (hv : CompactRepresentative v) :
    CompactRepresentative (u+v) := by
  have h := compact_sub hu (compact_neg v hv)
  simpa using h

theorem matrixField_compact (A : Fin 3 → Fin 3 → Test) (C : L2Vector) (j : Fin 3) :
    CompactRepresentative (matrixField A C j) := by
  apply compact_add
  · apply compact_add
    · exact cutoff_compact (A j 0) (C 0)
    · exact cutoff_compact (A j 1) (C 1)
  · exact cutoff_compact (A j 2) (C 2)

theorem weighted_matrix_tangential_partial (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DC : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hi : i ≠ 2)
    (hC : ∀ k, HasWeakPartial (C k) (DC k) i) :
    HasWeakPartial (mulWeight d hd (matrixField A C j))
      (mulWeight d hd (matrixField A DC j + matrixField (derivativeMatrix A hA i) C j)) i := by
  exact directional_weighted_tangential_partial d hd (matrixField A C j) _
    (matrixField_compact A C j) i hi (matrix_weak_partial A hA C DC i j hC)

end OQ14.Packet05WeightedMatrixDerivative
#print axioms OQ14.Packet05WeightedMatrixDerivative.compact_neg
#print axioms OQ14.Packet05WeightedMatrixDerivative.compact_add
#print axioms OQ14.Packet05WeightedMatrixDerivative.matrixField_compact
#print axioms OQ14.Packet05WeightedMatrixDerivative.weighted_matrix_tangential_partial

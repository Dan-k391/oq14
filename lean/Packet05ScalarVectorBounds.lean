import Packet05ScalarCutoffPairing
import Packet05ScalarEnergyBound
import WeakPoynting.InteriorTestDensity

/-! Quantitative Cauchy–Schwarz bounds for the three-component scalar
transmission energy and its smooth matrix factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarVectorBounds
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakPower
  OQ14.WeakTranslations OQ14.Packet05TensorCommutator OQ14.Packet05ScalarEnergyBound

theorem matrixField_norm (A : Fin 3 → Fin 3 → Test) (Q : L2Vector) (j : Fin 3)
    (a : ℝ) (ha : ∀ i x, ‖(A j i).function x‖ ≤ a) :
    ‖matrixField A Q j‖ ≤ a * (‖Q 0‖ + ‖Q 1‖ + ‖Q 2‖) := by
  have h0 := InteriorTestDensity.scaleL2_norm_le (A j 0).function (A j 0).regular.continuous (A j 0).compact (Q 0) (ha 0)
  have h1 := InteriorTestDensity.scaleL2_norm_le (A j 1).function (A j 1).regular.continuous (A j 1).compact (Q 1) (ha 1)
  have h2 := InteriorTestDensity.scaleL2_norm_le (A j 2).function (A j 2).regular.continuous (A j 2).compact (Q 2) (ha 2)
  let X0 := scaleL2 (A j 0).function (A j 0).regular.continuous (A j 0).compact (Q 0)
  let X1 := scaleL2 (A j 1).function (A j 1).regular.continuous (A j 1).compact (Q 1)
  let X2 := scaleL2 (A j 2).function (A j 2).regular.continuous (A j 2).compact (Q 2)
  have hn : ‖X0+X1+X2‖ ≤ ‖X0‖+‖X1‖+‖X2‖ :=
    (norm_add_le (X0+X1) X2).trans (add_le_add_right (norm_add_le X0 X1) _)
  change ‖X0+X1+X2‖ ≤ _
  nlinarith

theorem vector_pairing_norm (L V : L2Vector) :
    ‖∑ j : Fin 3, scalarProduct (L j) (conjScalar (V j))‖ ≤
      (∑ j : Fin 3, ‖L j‖) * (∑ j : Fin 3, ‖V j‖) := by
  calc
    _ ≤ ∑ j : Fin 3, ‖scalarProduct (L j) (conjScalar (V j))‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖L j‖ * (∑ k : Fin 3, ‖V k‖) := by
      apply Finset.sum_le_sum
      intro j hj
      have hv : ‖V j‖ ≤ ∑ k : Fin 3, ‖V k‖ :=
        Finset.single_le_sum (fun k _ => norm_nonneg (V k)) hj
      exact (scalarProduct_norm_le _ _).trans
        (mul_le_mul (le_refl _) ((conjugate_norm_le (V j)).trans hv) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [Finset.sum_mul]

end OQ14.Packet05ScalarVectorBounds
#print axioms OQ14.Packet05ScalarVectorBounds.matrixField_norm
#print axioms OQ14.Packet05ScalarVectorBounds.vector_pairing_norm

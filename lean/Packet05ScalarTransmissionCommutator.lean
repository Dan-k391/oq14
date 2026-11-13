import Packet05TensorCommutator

/-! The explicit lower-order matrix commutator in tangential difference
quotients of the scalar transmission flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarTransmissionCommutator
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator
  OQ14.Packet05TensorCommutator

def matrixResidual (A : Fin 3 → Fin 3 → Test) (C : L2Vector)
    (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (b : ℝ)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) : L2Scalar :=
  cutoffSource (A j 0) (C 0) i h hh b (hb j 0) +
  cutoffSource (A j 1) (C 1) i h hh b (hb j 1) +
  cutoffSource (A j 2) (C 2) i h hh b (hb j 2)

theorem matrix_quotient_decomposition (A : Fin 3 → Fin 3 → Test) (C : L2Vector)
    (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (b : ℝ)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    quotient (matrixField A C j) i h =
      matrixField A (fun l => quotient (C l) i h) j + matrixResidual A C i j h hh b hb := by
  unfold matrixField matrixResidual
  rw [quotient_add, quotient_add]
  rw [cutoff_quotient_decomposition (A j 0) (C 0) i h hh b (hb j 0),
    cutoff_quotient_decomposition (A j 1) (C 1) i h hh b (hb j 1),
    cutoff_quotient_decomposition (A j 2) (C 2) i h hh b (hb j 2)]
  abel

theorem matrixResidual_norm (A : Fin 3 → Fin 3 → Test) (C : L2Vector)
    (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (b : ℝ)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ‖matrixResidual A C i j h hh b hb‖ ≤ 3*b*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have h0 := cutoffSource_norm (A j 0) (C 0) i h hh b (hb j 0)
  have h1 := cutoffSource_norm (A j 1) (C 1) i h hh b (hb j 1)
  have h2 := cutoffSource_norm (A j 2) (C 2) i h hh b (hb j 2)
  have hn := (norm_add_le (cutoffSource (A j 0) (C 0) i h hh b (hb j 0) +
    cutoffSource (A j 1) (C 1) i h hh b (hb j 1))
    (cutoffSource (A j 2) (C 2) i h hh b (hb j 2))).trans
    (add_le_add_right (norm_add_le _ _) _)
  change ‖_ + _ + _‖ ≤ _
  nlinarith

end OQ14.Packet05ScalarTransmissionCommutator
#print axioms OQ14.Packet05ScalarTransmissionCommutator.matrix_quotient_decomposition
#print axioms OQ14.Packet05ScalarTransmissionCommutator.matrixResidual_norm

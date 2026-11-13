import Packet05ScalarTransmissionTest

/-! L² control of the coefficient and forcing residual appearing in the
actual tested scalar transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarResidualBound
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarTransmissionCommutator

theorem weight_norm_bound (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) :
    ‖mulWeight d hd u‖ ≤ (1+d)*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulWeight_ae d hd u] with x hx
  rw [hx, norm_mul]
  have h := FlatDifferenceCoercivity.dielectric_bounds d hd x
  have hw : ‖weight d x‖ ≤ 1+d := by
    simpa only [weight, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) h.1)] using h.2
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

theorem dielectric_matrix_residual_bound (A : Fin 3 → Fin 3 → Test) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ‖mulWeight d hd (matrixResidual A C i j h hh b hb) - quotient (F j) i h‖ ≤
      (1+d)*(3*b*(‖C 0‖+‖C 1‖+‖C 2‖)) + ‖quotient (F j) i h‖ := by
  have hm := matrixResidual_norm A C i j h hh b hb
  have hw := weight_norm_bound d hd (matrixResidual A C i j h hh b hb)
  have hc : 0 ≤ 1+d := by linarith
  exact (norm_sub_le _ _).trans (add_le_add_right
    (hw.trans (mul_le_mul_of_nonneg_left hm hc)) _)

end OQ14.Packet05ScalarResidualBound
#print axioms OQ14.Packet05ScalarResidualBound.weight_norm_bound
#print axioms OQ14.Packet05ScalarResidualBound.dielectric_matrix_residual_bound

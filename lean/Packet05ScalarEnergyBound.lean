import Packet05ScalarEnergyIdentity
import WeakPoynting.Translations

/-! Cauchy–Schwarz control of the residual side of the actual scalar energy
identity, with the coefficient and data norms explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarEnergyBound
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.WeakPower OQ14.WeakTranslations
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05ScalarCutoffTesting OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarTransmissionCommutator OQ14.Packet05TensorCommutator
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarEnergyIdentity OQ14.Packet05ScalarResidualBound

theorem conjugate_norm_le (u : L2Scalar) : ‖conjScalar u‖ ≤ ‖u‖ := by
  have h : ‖conjScalar u‖ ≤ 1 * ‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [conjScalar_ae u] with x hx
    rw [hx]
    simp
  simpa using h

theorem principal_energy_residual_bound (A : Fin 3 → Fin 3 → Test) (u : L2Scalar)
    (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) 0)
    (χ : Test) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ‖∑ j : Fin 3, scalarProduct
      (mulWeight d hd (matrixField A (fun l => quotient (C l) i h) j))
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j))‖ ≤
    ∑ j : Fin 3, ((1+d)*(3*b*(‖C 0‖+‖C 1‖+‖C 2‖)) + ‖quotient (F j) i h‖) *
      ‖cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j‖ := by
  rw [principal_energy_balance A u C F d hd hC hdiv χ i hi h hh b hb, norm_neg]
  calc
    _ ≤ ∑ j : Fin 3, ‖scalarProduct
        (mulWeight d hd (matrixResidual A C i j h hh b hb) - quotient (F j) i h)
        (conjScalar (cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      have hr := dielectric_matrix_residual_bound A C F d hd i j h hh b hb
      have ht := conjugate_norm_le (cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j)
      exact (scalarProduct_norm_le _ _).trans (mul_le_mul hr ht (norm_nonneg _) (le_trans (norm_nonneg _) hr))

end OQ14.Packet05ScalarEnergyBound
#print axioms OQ14.Packet05ScalarEnergyBound.conjugate_norm_le
#print axioms OQ14.Packet05ScalarEnergyBound.principal_energy_residual_bound

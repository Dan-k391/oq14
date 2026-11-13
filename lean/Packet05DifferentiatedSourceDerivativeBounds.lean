import Packet05DifferentiatedSourceBounds

/-! The second differentiated source has a controlled explicit derivative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05DifferentiatedSourceDerivativeBounds
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05TensorCommutator OQ14.Packet05FlatWeight
  OQ14.Packet05ScalarVectorBounds OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05DifferentiatedScalarEquation OQ14.Packet05DifferentiatedSourceBounds

theorem differentiated_source_derivative_norm
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (C TC DDF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i t j : Fin 3) (b c : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b)
    (hc : ∀ p q x, ‖dcoord (derivativeMatrix A hA2 i p q).function x t‖ ≤ c) :
    ‖DDF j - mulWeight d hd
      (matrixField (derivativeMatrix A hA2 i) TC j +
       matrixField (derivativeMatrix (derivativeMatrix A hA2 i)
         (OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i) t) C j)‖ ≤
      ‖DDF j‖ + (1+d) *
        (b*(‖TC 0‖+‖TC 1‖+‖TC 2‖) + c*(‖C 0‖+‖C 1‖+‖C 2‖)) := by
  let B := derivativeMatrix A hA2 i
  let hB := OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i
  have h1 := matrixField_norm B TC j b (fun k x => hb j k x)
  have h2 := matrixField_norm (derivativeMatrix B hB t) C j c (fun k x => hc j k x)
  have hm := norm_add_le (matrixField B TC j) (matrixField (derivativeMatrix B hB t) C j)
  have hw := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd
    (matrixField B TC j + matrixField (derivativeMatrix B hB t) C j)
  have hk : 0 ≤ 1+d := by linarith
  have he : ‖matrixField B TC j + matrixField (derivativeMatrix B hB t) C j‖ ≤
      b*(‖TC 0‖+‖TC 1‖+‖TC 2‖) + c*(‖C 0‖+‖C 1‖+‖C 2‖) := by linarith
  have he' := mul_le_mul_of_nonneg_left he hk
  exact (norm_sub_le _ _).trans (by nlinarith)

end OQ14.Packet05DifferentiatedSourceDerivativeBounds
#print axioms OQ14.Packet05DifferentiatedSourceDerivativeBounds.differentiated_source_derivative_norm

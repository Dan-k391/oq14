import Packet05NormalFluxNorms

/-! Bounds for differentiated sources in the conserved-flux estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferentiatedFluxNorm
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05TensorCommutator Packet05ScalarVectorBounds Packet05ScalarResidualBound
  Packet05MatrixWeakDerivative Packet05DifferentiatedScalarEquation

theorem differentiated_source_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (C Fi : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (b : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b) :
    ‖differentiatedSource A hA2 C Fi d hd i j‖ ≤
      ‖Fi j‖+(1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have hm := matrixField_norm (derivativeMatrix A hA2 i) C j b (by
    intro q x
    exact hb j q x)
  have hw := weight_norm_bound d hd (matrixField (derivativeMatrix A hA2 i) C j)
  have hs := norm_sub_le (Fi j) (Packet05FlatWeight.mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) C j))
  have hh := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 1+d)
  change ‖Fi j - Packet05FlatWeight.mulWeight d hd (matrixField (derivativeMatrix A hA2 i) C j)‖ ≤ _
  nlinarith

end OQ14.Packet05DifferentiatedFluxNorm
#print axioms OQ14.Packet05DifferentiatedFluxNorm.differentiated_source_norm

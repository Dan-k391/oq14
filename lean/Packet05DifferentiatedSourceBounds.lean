import Packet05CurlSourceH1
import Packet05ScalarResidualBound
import Packet05DifferentiatedSourceRegularity
import Packet05ScalarVectorBounds
import Packet05ScalarCutoffBound

/-! Explicit first differentiated transmission-source bounds. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05DifferentiatedSourceBounds
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05TensorCommutator OQ14.Packet05FlatWeight
  OQ14.Packet05ScalarVectorBounds OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05DifferentiatedScalarEquation OQ14.Packet05CurlSourceH1

theorem differentiated_source_norm (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (b : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b) :
    ‖differentiatedSource A hA C DF d hd i j‖ ≤
      ‖DF j‖ + (1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have hm := matrixField_norm (derivativeMatrix A hA i) C j b (fun k x => hb j k x)
  have hw := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd
    (matrixField (derivativeMatrix A hA i) C j)
  have hb0 : 0 ≤ 1+d := by linarith
  have hbound := mul_le_mul_of_nonneg_left hm hb0
  change ‖DF j - mulWeight d hd (matrixField (derivativeMatrix A hA i) C j)‖ ≤ _
  exact (norm_sub_le _ _).trans (by nlinarith)

theorem cutoff_product_norm (χ : Test) (u D : L2Scalar) (i : Fin 3) (a b : ℝ)
    (ha : ∀ x, ‖χ.function x‖ ≤ a) (hb : ∀ x, ‖dcoord χ.function x i‖ ≤ b) :
    ‖cutoffProductDerivative χ u D i‖ ≤ a*‖D‖ + b*‖u‖ := by
  unfold cutoffProductDerivative
  exact (norm_add_le _ _).trans (add_le_add
    (OQ14.InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact D ha)
    (OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord χ.function x i)
      (partial_continuous χ.regular i) (χ.compact.fderiv_apply ℝ (basis i)) u hb))

end OQ14.Packet05DifferentiatedSourceBounds
#print axioms OQ14.Packet05DifferentiatedSourceBounds.differentiated_source_norm
#print axioms OQ14.Packet05DifferentiatedSourceBounds.cutoff_product_norm

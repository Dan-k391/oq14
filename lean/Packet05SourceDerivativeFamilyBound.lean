import Packet05DifferentiatedSourceDerivativeBounds
import Packet05ForcingFamilyBound
import Packet05MixedCutoffSourceBounds

/-! Finite-sum bound for the derivative of the differentiated source. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05SourceDerivativeFamilyBound
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05TensorCommutator OQ14.Packet05FlatWeight
  OQ14.Packet05ScalarVectorBounds OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05DifferentiatedSourceDerivativeBounds

theorem differentiated_source_derivative_sum
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (C TC DDF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i t : Fin 3) (b c : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b)
    (hc : ∀ p q x, ‖dcoord (derivativeMatrix A hA2 i p q).function x t‖ ≤ c) :
    (∑ j : Fin 3, ‖DDF j - mulWeight d hd
      (matrixField (derivativeMatrix A hA2 i) TC j +
       matrixField (derivativeMatrix (derivativeMatrix A hA2 i)
         (OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i) t) C j)‖) ≤
      (∑ j : Fin 3, ‖DDF j‖) + 3*(1+d) *
        (b*(‖TC 0‖+‖TC 1‖+‖TC 2‖) + c*(‖C 0‖+‖C 1‖+‖C 2‖)) := by
  have h0 := differentiated_source_derivative_norm A hA2 hA3 C TC DDF d hd i t 0 b c hb hc
  have h1 := differentiated_source_derivative_norm A hA2 hA3 C TC DDF d hd i t 1 b c hb hc
  have h2 := differentiated_source_derivative_norm A hA2 hA3 C TC DDF d hd i t 2 b c hb hc
  simp only [Fin.sum_univ_three]
  linarith

end OQ14.Packet05SourceDerivativeFamilyBound
#print axioms OQ14.Packet05SourceDerivativeFamilyBound.differentiated_source_derivative_sum

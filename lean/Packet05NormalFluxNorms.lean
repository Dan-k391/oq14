import Packet05QuantitativeCutoffNorms
import Packet05NormalFluxArrays
import Packet05ScalarLocalizedFieldBounds

/-! Norm control for a tangential derivative of the actual graph flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05NormalFluxNorms
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05NormalFluxArrays Packet05ExplicitNormalFluxDerivative Packet05TensorCommutator
  Packet05ScalarVectorBounds Packet05ScalarResidualBound Packet05MatrixWeakDerivative
  Packet05DifferentiatedSourceRegularity

theorem tangent_flux_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F Ci Fi : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (a b : ℝ)
    (ha : ∀ p q x, ‖(A p q).function x‖ ≤ a)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b) :
    ‖tangentFlux A hA2 C F Ci Fi d hd i j‖ ≤
      (1+d)*(a*(‖Ci 0‖+‖Ci 1‖+‖Ci 2‖)+b*(‖C 0‖+‖C 1‖+‖C 2‖)) + ‖Fi j‖ := by
  have hmatrix := matrixField_norm A Ci j a (ha j)
  have hder := matrixField_norm (derivativeMatrix A hA2 i) C j b (by
    intro q x
    exact hb j q x)
  have hw := weight_norm_bound d hd
    (matrixField A Ci j + matrixField (derivativeMatrix A hA2 i) C j)
  have hadd := norm_add_le (matrixField A Ci j) (matrixField (derivativeMatrix A hA2 i) C j)
  have hsub := norm_sub_le (Packet05FlatWeight.mulWeight d hd
    (matrixField A Ci j + matrixField (derivativeMatrix A hA2 i) C j)) (Fi j)
  have hw' := mul_le_mul_of_nonneg_left (hadd.trans (add_le_add hmatrix hder)) (by linarith : 0 ≤ 1+d)
  change ‖Packet05FlatWeight.mulWeight d hd
    (matrixField A Ci j + matrixField (derivativeMatrix A hA2 i) C j) - Fi j‖ ≤ _
  linarith


theorem flux_norm (A : Fin 3 → Fin 3 → Test) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (j : Fin 3) (a : ℝ)
    (ha : ∀ p q x, ‖(A p q).function x‖ ≤ a) :
    ‖Packet05ScalarDielectricFlux.flux A C d hd j-F j‖ ≤
      (1+d)*a*(‖C 0‖+‖C 1‖+‖C 2‖)+‖F j‖ := by
  have hm := matrixField_norm A C j a (ha j)
  have hw := weight_norm_bound d hd (matrixField A C j)
  have hs := norm_sub_le (Packet05FlatWeight.mulWeight d hd (matrixField A C j)) (F j)
  have hh := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 1+d)
  change ‖Packet05FlatWeight.mulWeight d hd (matrixField A C j)-F j‖ ≤ _
  nlinarith

theorem source_derivative_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C Ct Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i t j : Fin 3) (b c : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b)
    (hc : ∀ p q x, ‖dcoord (derivativeMatrix A hA2 i p q).function x t‖ ≤ c) :
    ‖sourceDerivative A hA2 hA3 C Ct Fit d hd i t j‖ ≤
      ‖Fit j‖+(1+d)*(b*(‖Ct 0‖+‖Ct 1‖+‖Ct 2‖)+c*(‖C 0‖+‖C 1‖+‖C 2‖)) := by
  have hm := matrixField_norm (derivativeMatrix A hA2 i) Ct j b (by
    intro q x
    exact hb j q x)
  have hn := matrixField_norm (derivativeMatrix (derivativeMatrix A hA2 i)
    (derivativeMatrix_c2 A hA2 hA3 i) t) C j c (by
      intro q x
      exact hc j q x)
  have hw := weight_norm_bound d hd (matrixField (derivativeMatrix A hA2 i) Ct j +
    matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j)
  have hadd := norm_add_le (matrixField (derivativeMatrix A hA2 i) Ct j)
    (matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j)
  have hs := norm_sub_le (Fit j) (Packet05FlatWeight.mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) Ct j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j))
  have hh := mul_le_mul_of_nonneg_left (hadd.trans (add_le_add hm hn)) (by linarith : 0 ≤ 1+d)
  change ‖Fit j - Packet05FlatWeight.mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) Ct j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C j)‖ ≤ _
  linarith

theorem normal_derivative_array_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F C0 C1 F0 F1 : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (K0 K1 : ℝ)
    (h0 : ∀ j, ‖tangentFlux A hA2 C F C0 F0 d hd 0 j‖ ≤ K0)
    (h1 : ∀ j, ‖tangentFlux A hA2 C F C1 F1 d hd 1 j‖ ≤ K1) (i : Fin 3) :
    ‖normalDerivativeArray A hA2 C F C0 C1 F0 F1 d hd i‖ ≤ K0+K1 := by
  have hK0 : 0 ≤ K0 := (norm_nonneg _).trans (h0 0)
  have hK1 : 0 ≤ K1 := (norm_nonneg _).trans (h1 0)
  fin_cases i
  · change ‖tangentFlux A hA2 C F C0 F0 d hd 0 2‖ ≤ K0+K1
    linarith [h0 2]
  · change ‖tangentFlux A hA2 C F C1 F1 d hd 1 2‖ ≤ K0+K1
    linarith [h1 2]
  · change ‖(0 : L2Scalar)-tangentFlux A hA2 C F C0 F0 d hd 0 0-
      tangentFlux A hA2 C F C1 F1 d hd 1 1‖ ≤ K0+K1
    have h := norm_sub_le (-tangentFlux A hA2 C F C0 F0 d hd 0 0)
      (tangentFlux A hA2 C F C1 F1 d hd 1 1)
    simp only [norm_neg] at h
    simpa only [zero_sub] using h.trans (add_le_add (h0 0) (h1 1))

theorem first_flux_array_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F : L2Vector)
    (C1 F1 : Fin 3 → L2Vector) (d : ℝ) (hd : 0 ≤ d) (η : Test)
    (a b K0 K1 K : ℝ) (ha : ∀ x, ‖η.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord η.function x i‖ ≤ b)
    (h0 : ∀ j, ‖tangentFlux A hA2 C F (C1 0) (F1 0) d hd 0 j‖ ≤ K0)
    (h1 : ∀ j, ‖tangentFlux A hA2 C F (C1 1) (F1 1) d hd 1 j‖ ≤ K1)
    (hK : ‖Packet05ScalarDielectricFlux.flux A C d hd 2-F 2‖ ≤ K) (i : Fin 3) :
    ‖firstFluxArray A hA2 C F C1 F1 d hd η i‖ ≤ a*(K0+K1)+b*K := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have hn := normal_derivative_array_norm A hA2 C F (C1 0) (C1 1) (F1 0) (F1 1) d hd K0 K1 h0 h1 i
  have hm := Packet05QuantitativeCutoffNorms.first_array_norm
    (Packet05ScalarDielectricFlux.flux A C d hd 2-F 2)
    (normalDerivativeArray A hA2 C F (C1 0) (C1 1) (F1 0) (F1 1) d hd) η a b ha hb i
  exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left hn ha0) (mul_le_mul_of_nonneg_left hK hb0))

theorem second_flux_array_norm (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (χ : Test) (i j : Fin 3) (a b K0 K1 K : ℝ)
    (ha : ∀ x, ‖χ.function x‖ ≤ a) (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (h0 : ∀ q, ‖tangentFlux A hA2 (C1 i) (Packet05DifferentiatedScalarEquation.differentiatedSource A hA2 C (F1 i) d hd i)
      (C2 i 0) (sourceDerivative A hA2 hA3 C (C1 0) (F2 i 0) d hd i 0) d hd 0 q‖ ≤ K0)
    (h1 : ∀ q, ‖tangentFlux A hA2 (C1 i) (Packet05DifferentiatedScalarEquation.differentiatedSource A hA2 C (F1 i) d hd i)
      (C2 i 1) (sourceDerivative A hA2 hA3 C (C1 1) (F2 i 1) d hd i 1) d hd 1 q‖ ≤ K1)
    (hK : ‖Packet05ScalarDielectricFlux.flux A (C1 i) d hd 2-
      Packet05DifferentiatedScalarEquation.differentiatedSource A hA2 C (F1 i) d hd i 2‖ ≤ K) :
    ‖secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i j‖ ≤ a*(K0+K1)+b*K := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  let R := Packet05DifferentiatedScalarEquation.differentiatedSource A hA2 C (F1 i) d hd i
  let R0 := sourceDerivative A hA2 hA3 C (C1 0) (F2 i 0) d hd i 0
  let R1 := sourceDerivative A hA2 hA3 C (C1 1) (F2 i 1) d hd i 1
  have hn := normal_derivative_array_norm A hA2 (C1 i) R (C2 i 0) (C2 i 1) R0 R1 d hd K0 K1 h0 h1 j
  have hm := Packet05QuantitativeCutoffNorms.first_array_norm
    (Packet05ScalarDielectricFlux.flux A (C1 i) d hd 2-R 2)
    (normalDerivativeArray A hA2 (C1 i) R (C2 i 0) (C2 i 1) R0 R1 d hd) χ a b ha hb j
  exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left hn ha0) (mul_le_mul_of_nonneg_left hK hb0))
end OQ14.Packet05NormalFluxNorms
#print axioms OQ14.Packet05NormalFluxNorms.tangent_flux_norm
#print axioms OQ14.Packet05NormalFluxNorms.flux_norm
#print axioms OQ14.Packet05NormalFluxNorms.source_derivative_norm
#print axioms OQ14.Packet05NormalFluxNorms.normal_derivative_array_norm
#print axioms OQ14.Packet05NormalFluxNorms.first_flux_array_norm
#print axioms OQ14.Packet05NormalFluxNorms.second_flux_array_norm

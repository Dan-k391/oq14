import Packet05ExplicitLocalizedForcing
import Packet05DifferentiatedSourceBounds

/-! Quantitative bounds for the explicit localized forcing derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalizedForcingNorm
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05RegionalScalarLocalization OQ14.MaxwellCutoffCommutator
  OQ14.Packet05CurlSourceH1 OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator
  OQ14.Packet05MatrixWeakDerivative OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05DifferentiatedSourceBounds OQ14.Packet05ScalarVectorBounds

theorem force_derivative_norm (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (v Dv : L2Scalar) (F DF : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3)
    (a b α β γ : ℝ)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hb : ∀ j k x, ‖dcoord (A j k).function x i‖ ≤ b)
    (hα : ∀ x, ‖ζ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord ζ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ k x, ‖dcoord (derivativeCutoff ζ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hζ2) k).function x i‖ ≤ γ) :
    ‖forceDerivative ζ hζ2 A hA2 v Dv F DF d hd i j‖ ≤
      α*‖DF j‖ + β*‖F j‖ + (1+d)*
        (3*a*(β*‖Dv‖+γ*‖v‖) + 3*b*β*‖v‖) := by
  let hζc2 := Complex.ofRealCLM.contDiff.comp hζ2
  let R : L2Vector := fun k => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Dv i
  let T : L2Vector := cutoffCorrection ζ v
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hd0 : 0 ≤ 1+d := by linarith
  have hR (k : Fin 3) : ‖R k‖ ≤ β*‖Dv‖+γ*‖v‖ :=
    cutoff_product_norm (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Dv i β γ (hβ k) (hγ k)
  have hT (k : Fin 3) : ‖T k‖ ≤ β*‖v‖ := by
    exact OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord ζ.complexTest.function x k)
      (partial_continuous ζ.complexTest.regular k)
      (ζ.complexTest.compact.fderiv_apply ℝ (basis k)) v (hβ k)
  have hm1 := matrixField_norm A R j a (ha j)
  have hm2 := matrixField_norm (derivativeMatrix A hA2 i) T j b (fun k x => hb j k x)
  have hsumR : ‖R 0‖+‖R 1‖+‖R 2‖ ≤ 3*(β*‖Dv‖+γ*‖v‖) := by linarith [hR 0,hR 1,hR 2]
  have hsumT : ‖T 0‖+‖T 1‖+‖T 2‖ ≤ 3*β*‖v‖ := by linarith [hT 0,hT 1,hT 2]
  have hma := mul_le_mul_of_nonneg_left hsumR ha0
  have hmb := mul_le_mul_of_nonneg_left hsumT hb0
  have hw := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd
    (matrixField A R j + matrixField (derivativeMatrix A hA2 i) T j)
  have hm := norm_add_le (matrixField A R j) (matrixField (derivativeMatrix A hA2 i) T j)
  have hprod := cutoff_product_norm ζ.complexTest.toTest (F j) (DF j) i α β hα (hβ i)
  have hres : ‖matrixField A R j + matrixField (derivativeMatrix A hA2 i) T j‖ ≤
      3*a*(β*‖Dv‖+γ*‖v‖) + 3*b*β*‖v‖ := by nlinarith
  have hw' := mul_le_mul_of_nonneg_left hres hd0
  change ‖cutoffProductDerivative ζ.complexTest.toTest (F j) (DF j) i +
    mulWeight d hd (matrixField A R j + matrixField (derivativeMatrix A hA2 i) T j)‖ ≤ _
  exact (norm_add_le _ _).trans (by nlinarith)


theorem localized_gradient_norm (ζ : RealTest Set.univ) (v : L2Scalar) (G : L2Vector)
    (α β : ℝ) (hα : ∀ x, ‖ζ.complexTest.function x‖ ≤ α)
    (hβ : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ β) (j : Fin 3) :
    ‖localizedGradient ζ v G j‖ ≤ α*‖G j‖ + β*‖v‖ := by
  have h1 := OQ14.InteriorTestDensity.scaleL2_norm_le ζ.complexTest.function
    ζ.complexTest.regular.continuous ζ.complexTest.compact (G j) hα
  have h2 := OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord ζ.complexTest.function x j)
    (partial_continuous ζ.complexTest.regular j) (ζ.complexTest.compact.fderiv_apply ℝ (basis j)) v (hβ j)
  change ‖scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact (G j) +
    scaleL2 (fun x => dcoord ζ.complexTest.function x j) (partial_continuous ζ.complexTest.regular j)
      (ζ.complexTest.compact.fderiv_apply ℝ (basis j)) v‖ ≤ _
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end OQ14.Packet05LocalizedForcingNorm
#print axioms OQ14.Packet05LocalizedForcingNorm.force_derivative_norm

#print axioms OQ14.Packet05LocalizedForcingNorm.localized_gradient_norm

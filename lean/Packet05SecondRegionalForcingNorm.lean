import Packet05ExplicitSecondForcing
import Packet05DifferentiatedSourceBounds
import Packet05MixedCutoffSourceBounds
import Packet05ScalarVectorBounds
import Packet05ScalarResidualBound

/-! Explicit original-data bound for the second regional forcing commutator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05SecondRegionalForcingNorm
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalScalarLocalization OQ14.Packet05ScalarPrincipalLocalization
  OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1 OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05DifferentiatedSourceRegularity OQ14.Packet05ExplicitSecondForcing
  OQ14.Packet05DifferentiatedSourceBounds OQ14.Packet05MixedCutoffSourceBounds
  OQ14.Packet05ScalarVectorBounds

theorem second_forcing_norm (ζ : RealTest univ) (hζ2 : ContDiff ℝ 2 ζ.function)
    (hζ3 : ContDiff ℝ 3 ζ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (v Di Dt Dit : L2Scalar) (F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (i t j : Fin 3) (a b c α β γ δ : ℝ)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hb : ∀ j k l x, ‖dcoord (A j k).function x l‖ ≤ b)
    (hc : ∀ j k x, ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hα : ∀ x, ‖ζ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord ζ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ k l x, ‖dcoord (derivativeCutoff ζ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hζ2) k).function x l‖ ≤ γ)
    (hδ : ∀ k x, ‖dcoord (derivativeCutoff
      (derivativeCutoff ζ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hζ2) k)
      (by
        have hh : ContDiff ℝ 2 (fderiv ℝ ζ.complexTest.function) :=
          (contDiff_succ_iff_fderiv (n := 2)).mp (Complex.ofRealCLM.contDiff.comp hζ3) |>.2.2
        exact hh.clm_apply contDiff_const) i).function x t‖ ≤ δ) :
    ‖forceSecondDerivative ζ hζ2 hζ3 A hA2 hA3 v Di Dt Dit F Fi Ft Fit d hd i t j‖ ≤
      α*‖Fit j‖ + β*(‖Fi j‖+‖Ft j‖) + γ*‖F j‖ + (1+d)*3*
        (a*(β*‖Dit‖ + γ*(‖Di‖+‖Dt‖) + δ*‖v‖) +
          b*(β*‖Di‖+γ*‖v‖) + b*(β*‖Dt‖+γ*‖v‖) + c*β*‖v‖) := by
  let hζc2 := Complex.ofRealCLM.contDiff.comp hζ2
  let hζc3 := Complex.ofRealCLM.contDiff.comp hζ3
  let hder2 (k : Fin 3) : ContDiff ℝ 2 (derivativeCutoff ζ.complexTest.toTest hζc2 k).function := by
    have hh : ContDiff ℝ 2 (fderiv ℝ ζ.complexTest.function) :=
      (contDiff_succ_iff_fderiv (n := 2)).mp hζc3 |>.2.2
    exact hh.clm_apply contDiff_const
  let R : L2Vector := fun k => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Di i
  let Rt : L2Vector := fun k => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 k) Di Dit t +
    cutoffProductDerivative (derivativeCutoff (derivativeCutoff ζ.complexTest.toTest hζc2 k) (hder2 k) i) v Dt t
  let Tcorr : L2Vector := fun k => cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Dt t
  let Ai := derivativeMatrix A hA2 i
  let hAi := derivativeMatrix_c2 A hA2 hA3 i
  let HB := cutoffProductDerivative ζ.complexTest.toTest (Fi j) (Fit j) t +
    cutoffProductDerivative (derivativeCutoff ζ.complexTest.toTest hζc2 i) (F j) (Ft j) t
  let W0 := matrixField A Rt j + matrixField (derivativeMatrix A hA2 t) R j
  let W1 := matrixField Ai Tcorr j + matrixField (derivativeMatrix Ai hAi t) (cutoffCorrection ζ v) j
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hγ0 : 0 ≤ γ := (norm_nonneg _).trans (hγ 0 0 0)
  have hd0 : 0 ≤ 1+d := by linarith
  have hR (k : Fin 3) : ‖R k‖ ≤ β*‖Di‖+γ*‖v‖ :=
    cutoff_product_norm (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Di i β γ (hβ k) (hγ k i)
  have hRt (k : Fin 3) : ‖Rt k‖ ≤ β*‖Dit‖+γ*(‖Di‖+‖Dt‖)+δ*‖v‖ := by
    have hh := mixed_cutoff_product_norm (derivativeCutoff ζ.complexTest.toTest hζc2 k) (hder2 k)
      v Di Dt Dit i t β γ δ (hβ k) (hγ k) (hδ k)
    dsimp only [Rt]
    nlinarith
  have hTc (k : Fin 3) : ‖Tcorr k‖ ≤ β*‖Dt‖+γ*‖v‖ :=
    cutoff_product_norm (derivativeCutoff ζ.complexTest.toTest hζc2 k) v Dt t β γ (hβ k) (hγ k t)
  have hC (k : Fin 3) : ‖cutoffCorrection ζ v k‖ ≤ β*‖v‖ := by
    exact OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord ζ.complexTest.function x k)
      (partial_continuous ζ.complexTest.regular k) (ζ.complexTest.compact.fderiv_apply ℝ (basis k)) v (hβ k)
  have hHB : ‖HB‖ ≤ α*‖Fit j‖+β*(‖Fi j‖+‖Ft j‖)+γ*‖F j‖ := by
    have hh := mixed_cutoff_product_norm ζ.complexTest.toTest hζc2 (F j) (Fi j) (Ft j) (Fit j) i t α β γ hα hβ (hγ i t)
    dsimp only [HB]
    nlinarith
  have hRsum : ‖R 0‖+‖R 1‖+‖R 2‖ ≤ 3*(β*‖Di‖+γ*‖v‖) := by linarith [hR 0,hR 1,hR 2]
  have hRtsum : ‖Rt 0‖+‖Rt 1‖+‖Rt 2‖ ≤ 3*(β*‖Dit‖+γ*(‖Di‖+‖Dt‖)+δ*‖v‖) := by linarith [hRt 0,hRt 1,hRt 2]
  have hTsum : ‖Tcorr 0‖+‖Tcorr 1‖+‖Tcorr 2‖ ≤ 3*(β*‖Dt‖+γ*‖v‖) := by linarith [hTc 0,hTc 1,hTc 2]
  have hCsum : ‖cutoffCorrection ζ v 0‖+‖cutoffCorrection ζ v 1‖+‖cutoffCorrection ζ v 2‖ ≤ 3*β*‖v‖ := by linarith [hC 0,hC 1,hC 2]
  have hm0 := matrixField_norm A Rt j a (ha j)
  have hm1 := matrixField_norm (derivativeMatrix A hA2 t) R j b (fun k x => hb j k t x)
  have hm2 := matrixField_norm Ai Tcorr j b (fun k x => hb j k i x)
  have hm3 := matrixField_norm (derivativeMatrix Ai hAi t) (cutoffCorrection ζ v) j c (fun k x => hc j k x)
  have h0 := mul_le_mul_of_nonneg_left hRtsum ha0
  have h1 := mul_le_mul_of_nonneg_left hRsum hb0
  have h2 := mul_le_mul_of_nonneg_left hTsum hb0
  have h3 := mul_le_mul_of_nonneg_left hCsum hc0
  have hW0 : ‖W0‖ ≤ 3*a*(β*‖Dit‖+γ*(‖Di‖+‖Dt‖)+δ*‖v‖) + 3*b*(β*‖Di‖+γ*‖v‖) := by
    exact (norm_add_le _ _).trans (by nlinarith)
  have hW1 : ‖W1‖ ≤ 3*b*(β*‖Dt‖+γ*‖v‖) + 3*c*β*‖v‖ := by
    exact (norm_add_le _ _).trans (by nlinarith)
  have hw0 := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd W0
  have hw1 := OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd W1
  have hw0' := mul_le_mul_of_nonneg_left hW0 hd0
  have hw1' := mul_le_mul_of_nonneg_left hW1 hd0
  have hn := norm_add_le (HB+mulWeight d hd W0) (mulWeight d hd W1)
  have hn' := norm_add_le HB (mulWeight d hd W0)
  change ‖HB+mulWeight d hd W0+mulWeight d hd W1‖ ≤ _
  nlinarith

end OQ14.Packet05SecondRegionalForcingNorm
#print axioms OQ14.Packet05SecondRegionalForcingNorm.second_forcing_norm

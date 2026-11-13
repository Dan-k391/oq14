import Packet05CutoffFamilyBound
import Packet05EnergyEnvelope

/-! Original-data bound for the explicit second-iteration forcing array. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05SecondForcingOriginalBound
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05DifferentiatedScalarEquation
  OQ14.Packet05TensorCommutator OQ14.Packet05FlatWeight OQ14.Packet05MatrixWeakDerivative
  OQ14.Packet05LocalizedForcingBootstrap OQ14.Packet05ForcingFamilyBound
  OQ14.Packet05SourceDerivativeFamilyBound OQ14.Packet05CutoffFamilyBound

theorem second_forcing_original_bound (τ κ : RealTest univ)
    (hτ2 : ContDiff ℝ 2 τ.function) (hκ2 : ContDiff ℝ 2 κ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C DC TC F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i t : Fin 3)
    (a b c α β γ αk βk γk : ℝ)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hb : ∀ j k l x, ‖dcoord (A j k).function x l‖ ≤ b)
    (hc : ∀ j k x, ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hα : ∀ x, ‖τ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord τ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ x, ‖dcoord (derivativeCutoff τ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hτ2) i).function x t‖ ≤ γ)
    (hαk : ∀ x, ‖κ.complexTest.function x‖ ≤ αk)
    (hβk : ∀ k x, ‖dcoord κ.complexTest.function x k‖ ≤ βk)
    (hγk : ∀ k x, ‖dcoord (derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) k).function x t‖ ≤ γk) :
    let P := ∑ j : Fin 3, ‖C j‖
    let Pi := ∑ j : Fin 3, ‖DC j‖
    let Pt := ∑ j : Fin 3, ‖TC j‖
    let P0 := ∑ j : Fin 3, ‖F j‖
    let P1 := ∑ j : Fin 3, ‖Fi j‖
    let P2 := ∑ j : Fin 3, ‖Ft j‖
    let P12 := ∑ j : Fin 3, ‖Fit j‖
    let C' := cutVector τ C
    let DF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (Fi j) i
    let DDF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (Fi j) (Fit j) t +
      cutoffProductDerivative (derivativeCutoff τ.complexTest.toTest
        (Complex.ofRealCLM.contDiff.comp hτ2) i) (F j) (Ft j) t
    let R := differentiatedSource A hA2 C' DF d hd i
    let DR : L2Vector := fun j => DDF j - mulWeight d hd
      (matrixField (derivativeMatrix A hA2 i) TC j +
        matrixField (derivativeMatrix (derivativeMatrix A hA2 i)
          (OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i) t) C' j)
    (∑ j : Fin 3, ‖forceDerivative κ hκ2 A hA2 (C i) (DC t) R DR d hd t j‖) ≤
      αk*(α*P12 + β*(P1+P2) + γ*P0 + 3*(1+d)*(b*Pt + c*α*P)) +
      βk*(α*P1+β*P0+3*(1+d)*b*α*P) +
      3*(1+d)*(3*a*(βk*Pi+γk*P)+3*b*βk*P) := by
  dsimp only
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hγ0 : 0 ≤ γ := (norm_nonneg _).trans (hγ 0)
  have hαk0 : 0 ≤ αk := (norm_nonneg _).trans (hαk 0)
  have hβk0 : 0 ≤ βk := (norm_nonneg _).trans (hβk 0 0)
  have hγk0 : 0 ≤ γk := (norm_nonneg _).trans (hγk 0 0)
  have hp0 : 0 ≤ 1+d := by linarith
  let C' := cutVector τ C
  let DF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (Fi j) i
  let DDF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (Fi j) (Fit j) t +
    cutoffProductDerivative (derivativeCutoff τ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hτ2) i) (F j) (Ft j) t
  let R := differentiatedSource A hA2 C' DF d hd i
  let DR : L2Vector := fun j => DDF j - mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) TC j + matrixField
      (derivativeMatrix (derivativeMatrix A hA2 i)
        (OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i) t) C' j)
  have hC' := cut_vector_sum τ C α hα
  have hDF := first_source_sum τ.complexTest.toTest F Fi i α β hα (hβ i)
  have hDDF := mixed_source_sum τ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hτ2)
    F Fi Ft Fit i t α β γ hα hβ hγ
  have hR := differentiated_source_sum A hA2 C' DF d hd i b (fun j k x => hb j k i x)
  have hDR := differentiated_source_derivative_sum A hA2 hA3 C' TC DDF d hd i t b c (fun j k x => hb j k i x) hc
  have hJ := force_derivative_sum κ hκ2 A hA2 (C i) (DC t) R DR d hd t a b αk βk γk ha
    (fun j k x => hb j k t x) hαk hβk hγk
  have hi : ‖C i‖ ≤ ∑ j : Fin 3, ‖C j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (C j)) (Finset.mem_univ i)
  have ht : ‖DC t‖ ≤ ∑ j : Fin 3, ‖DC j‖ := Finset.single_le_sum (fun j _ => norm_nonneg (DC j)) (Finset.mem_univ t)
  have hRbound : (∑ j : Fin 3, ‖R j‖) ≤
      α*(∑ j : Fin 3, ‖Fi j‖) + β*(∑ j : Fin 3, ‖F j‖) +
        3*(1+d)*b*α*(∑ j : Fin 3, ‖C j‖) := by
    calc
      _ ≤ (∑ j : Fin 3, ‖DF j‖) + 3*(1+d)*b*(∑ j : Fin 3, ‖C' j‖) := by
        simpa only [Fin.sum_univ_three] using hR
      _ ≤ _ := by
        have hcSum : (∑ j : Fin 3, ‖C' j‖) ≤ α*(∑ j : Fin 3, ‖C j‖) := by
          simpa only [Fin.sum_univ_three] using hC'
        have hp := mul_le_mul_of_nonneg_left hcSum (show 0 ≤ 3*(1+d)*b by positivity)
        dsimp only [DF] at *
        nlinarith
  have hDRbound : (∑ j : Fin 3, ‖DR j‖) ≤
      α*(∑ j : Fin 3, ‖Fit j‖) + β*((∑ j : Fin 3, ‖Fi j‖)+(∑ j : Fin 3, ‖Ft j‖)) +
        γ*(∑ j : Fin 3, ‖F j‖) + 3*(1+d)*(b*(∑ j : Fin 3, ‖TC j‖) + c*α*(∑ j : Fin 3, ‖C j‖)) := by
    calc
      _ ≤ (∑ j : Fin 3, ‖DDF j‖) + 3*(1+d)*(b*(∑ j : Fin 3, ‖TC j‖) + c*(∑ j : Fin 3, ‖C' j‖)) := by
        simpa only [Fin.sum_univ_three] using hDR
      _ ≤ _ := by
        have hcSum : (∑ j : Fin 3, ‖C' j‖) ≤ α*(∑ j : Fin 3, ‖C j‖) := by
          simpa only [Fin.sum_univ_three] using hC'
        have hp := mul_le_mul_of_nonneg_left hcSum (show 0 ≤ 3*(1+d)*c by positivity)
        dsimp only [DDF] at *
        nlinarith
  calc
    _ ≤ αk*(∑ j : Fin 3, ‖DR j‖) + βk*(∑ j : Fin 3, ‖R j‖) + 3*(1+d)*
        (3*a*(βk*‖DC t‖+γk*‖C i‖) + 3*b*βk*‖C i‖) := hJ
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left hDRbound hαk0
      have h2 := mul_le_mul_of_nonneg_left hRbound hβk0
      have h3 := mul_le_mul_of_nonneg_left ht hβk0
      have h4 := mul_le_mul_of_nonneg_left hi hγk0
      have h5 := mul_le_mul_of_nonneg_left hi (show 0 ≤ 3*b*βk by positivity)
      have h6 : 3*a*(βk*‖DC t‖+γk*‖C i‖)+3*b*βk*‖C i‖ ≤
          3*a*(βk*(∑ j : Fin 3, ‖DC j‖)+γk*(∑ j : Fin 3, ‖C j‖)) +
          3*b*βk*(∑ j : Fin 3, ‖C j‖) := by
        have hh := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (show 0 ≤ 3*a by positivity)
        linarith
      have h7 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ 3*(1+d) by positivity)
      linarith

end OQ14.Packet05SecondForcingOriginalBound
#print axioms OQ14.Packet05SecondForcingOriginalBound.second_forcing_original_bound

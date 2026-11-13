import Packet05RegionalLocalizedNorm
import Packet05LocalizedForcingNorm

/-! Uniform first tangential derivatives of the regional cutoff forcing. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05RegionalFirstForcingUniform
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05LocalizedForcingNorm

theorem first_forcing_uniform (κ : RealTest univ) (hκ2 : ContDiff ℝ 2 κ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (u : L2Scalar) (C F Fi : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3)
    (U P F0 F1 a b α β γ : ℝ)
    (hU : ‖u‖ ≤ U) (hP : ‖C i‖ ≤ P) (hF0 : ‖F j‖ ≤ F0) (hF1 : ‖Fi j‖ ≤ F1)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hb : ∀ j k x, ‖dcoord (A j k).function x i‖ ≤ b)
    (hα : ∀ x, ‖κ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord κ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ k x, ‖dcoord (derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) k).function x i‖ ≤ γ) :
    ‖forceDerivative κ hκ2 A hA2 u (C i) F Fi d hd i j‖ ≤
      α*F1 + β*F0 + (1+d)*(3*a*(β*P+γ*U)+3*b*β*U) := by
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hγ0 : 0 ≤ γ := (norm_nonneg _).trans (hγ 0 0)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0)
  have hraw := force_derivative_norm κ hκ2 A hA2 u (C i) F Fi d hd i j a b α β γ ha hb hα hβ hγ
  have h1 := mul_le_mul_of_nonneg_left hF1 hα0
  have h2 := mul_le_mul_of_nonneg_left hF0 hβ0
  have h3 := mul_le_mul_of_nonneg_left hP hβ0
  have h4 := mul_le_mul_of_nonneg_left hU hγ0
  have h5 := mul_le_mul_of_nonneg_left (add_le_add h3 h4) (show 0 ≤ 3*a by positivity)
  have h6 := mul_le_mul_of_nonneg_left hU (show 0 ≤ 3*b*β by positivity)
  have h7 : 3*a*(β*‖C i‖+γ*‖u‖)+3*b*β*‖u‖ ≤ 3*a*(β*P+γ*U)+3*b*β*U := by linarith
  have h8 := mul_le_mul_of_nonneg_left h7 (show 0 ≤ 1+d by linarith)
  exact hraw.trans (by linarith)

end OQ14.Packet05RegionalFirstForcingUniform
#print axioms OQ14.Packet05RegionalFirstForcingUniform.first_forcing_uniform

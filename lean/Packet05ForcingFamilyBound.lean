import Packet05LocalizedForcingNorm
import Packet05DifferentiatedSourceBounds

/-! Finite-sum forcing bounds used by the second tangential energy estimate. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ForcingFamilyBound
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05LocalizedForcingNorm OQ14.Packet05DifferentiatedSourceBounds

theorem force_derivative_sum (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (v Dv : L2Scalar) (F DF : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i : Fin 3)
    (a b α β γ : ℝ)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hb : ∀ j k x, ‖dcoord (A j k).function x i‖ ≤ b)
    (hα : ∀ x, ‖ζ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord ζ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ k x, ‖dcoord (derivativeCutoff ζ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hζ2) k).function x i‖ ≤ γ) :
    (∑ j : Fin 3, ‖forceDerivative ζ hζ2 A hA2 v Dv F DF d hd i j‖) ≤
      α*(∑ j : Fin 3, ‖DF j‖) + β*(∑ j : Fin 3, ‖F j‖) + 3*(1+d)*
        (3*a*(β*‖Dv‖+γ*‖v‖) + 3*b*β*‖v‖) := by
  have h0 := force_derivative_norm ζ hζ2 A hA2 v Dv F DF d hd i 0 a b α β γ ha hb hα hβ hγ
  have h1 := force_derivative_norm ζ hζ2 A hA2 v Dv F DF d hd i 1 a b α β γ ha hb hα hβ hγ
  have h2 := force_derivative_norm ζ hζ2 A hA2 v Dv F DF d hd i 2 a b α β γ ha hb hα hβ hγ
  simp only [Fin.sum_univ_three]
  linarith

theorem differentiated_source_sum (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C DF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i : Fin 3) (b : ℝ)
    (hb : ∀ p q x, ‖dcoord (A p q).function x i‖ ≤ b) :
    (∑ j : Fin 3, ‖OQ14.Packet05DifferentiatedScalarEquation.differentiatedSource A hA C DF d hd i j‖) ≤
      (∑ j : Fin 3, ‖DF j‖) + 3*(1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have h0 := differentiated_source_norm A hA C DF d hd i 0 b hb
  have h1 := differentiated_source_norm A hA C DF d hd i 1 b hb
  have h2 := differentiated_source_norm A hA C DF d hd i 2 b hb
  simp only [Fin.sum_univ_three]
  linarith

end OQ14.Packet05ForcingFamilyBound
#print axioms OQ14.Packet05ForcingFamilyBound.force_derivative_sum
#print axioms OQ14.Packet05ForcingFamilyBound.differentiated_source_sum

import Packet05SourceDerivativeFamilyBound
import Packet05ScalarPrincipalLocalization

/-! The cutoff product bounds summed across all original source components. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffFamilyBound
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1
  OQ14.Packet05DifferentiatedSourceBounds OQ14.Packet05MixedCutoffSourceBounds
  OQ14.Packet05ScalarPrincipalLocalization

theorem cut_vector_sum (τ : RealTest univ) (C : L2Vector) (α : ℝ)
    (hα : ∀ x, ‖τ.complexTest.function x‖ ≤ α) :
    (∑ j : Fin 3, ‖cutVector τ C j‖) ≤ α*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have h0 := OQ14.InteriorTestDensity.scaleL2_norm_le τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 0) hα
  have h1 := OQ14.InteriorTestDensity.scaleL2_norm_le τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 1) hα
  have h2 := OQ14.InteriorTestDensity.scaleL2_norm_le τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 2) hα
  simp only [Fin.sum_univ_three]
  change ‖scaleL2 τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 0)‖ +
    ‖scaleL2 τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 1)‖ +
    ‖scaleL2 τ.complexTest.function τ.complexTest.regular.continuous τ.complexTest.compact (C 2)‖ ≤ _
  linarith

theorem first_source_sum (τ : Test) (F Fi : L2Vector) (i : Fin 3) (α β : ℝ)
    (hα : ∀ x, ‖τ.function x‖ ≤ α) (hβ : ∀ x, ‖dcoord τ.function x i‖ ≤ β) :
    (∑ j : Fin 3, ‖cutoffProductDerivative τ (F j) (Fi j) i‖) ≤
      α*(∑ j : Fin 3, ‖Fi j‖) + β*(∑ j : Fin 3, ‖F j‖) := by
  have h0 := cutoff_product_norm τ (F 0) (Fi 0) i α β hα hβ
  have h1 := cutoff_product_norm τ (F 1) (Fi 1) i α β hα hβ
  have h2 := cutoff_product_norm τ (F 2) (Fi 2) i α β hα hβ
  simp only [Fin.sum_univ_three]
  linarith

theorem mixed_source_sum (τ : Test) (hτ2 : ContDiff ℝ 2 τ.function)
    (F Fi Ft Fit : L2Vector) (i t : Fin 3) (α β γ : ℝ)
    (hα : ∀ x, ‖τ.function x‖ ≤ α) (hβ : ∀ k x, ‖dcoord τ.function x k‖ ≤ β)
    (hγ : ∀ x, ‖dcoord (derivativeCutoff τ hτ2 i).function x t‖ ≤ γ) :
    (∑ j : Fin 3, ‖cutoffProductDerivative τ (Fi j) (Fit j) t +
      cutoffProductDerivative (derivativeCutoff τ hτ2 i) (F j) (Ft j) t‖) ≤
      α*(∑ j : Fin 3, ‖Fit j‖) + β*((∑ j : Fin 3, ‖Fi j‖)+(∑ j : Fin 3, ‖Ft j‖)) +
        γ*(∑ j : Fin 3, ‖F j‖) := by
  have h0 := mixed_cutoff_product_norm τ hτ2 (F 0) (Fi 0) (Ft 0) (Fit 0) i t α β γ hα hβ hγ
  have h1 := mixed_cutoff_product_norm τ hτ2 (F 1) (Fi 1) (Ft 1) (Fit 1) i t α β γ hα hβ hγ
  have h2 := mixed_cutoff_product_norm τ hτ2 (F 2) (Fi 2) (Ft 2) (Fit 2) i t α β γ hα hβ hγ
  simp only [Fin.sum_univ_three]
  linarith

end OQ14.Packet05CutoffFamilyBound
#print axioms OQ14.Packet05CutoffFamilyBound.cut_vector_sum
#print axioms OQ14.Packet05CutoffFamilyBound.first_source_sum
#print axioms OQ14.Packet05CutoffFamilyBound.mixed_source_sum

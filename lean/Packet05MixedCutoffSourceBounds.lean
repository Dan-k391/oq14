import Packet05DifferentiatedSourceDerivativeBounds
import Packet05CurlSourceH1
import MaxwellCutoffCommutator

/-! Explicit mixed cutoff derivative bounds for the original source arrays. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05MixedCutoffSourceBounds
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator OQ14.Packet05CurlSourceH1
  OQ14.Packet05DifferentiatedSourceBounds

theorem mixed_cutoff_product_norm (τ : Test) (hτ2 : ContDiff ℝ 2 τ.function)
    (F Fi Ft Fit : L2Scalar) (i t : Fin 3) (α β γ : ℝ)
    (hα : ∀ x, ‖τ.function x‖ ≤ α) (hβ : ∀ k x, ‖dcoord τ.function x k‖ ≤ β)
    (hγ : ∀ x, ‖dcoord (derivativeCutoff τ hτ2 i).function x t‖ ≤ γ) :
    ‖cutoffProductDerivative τ Fi Fit t +
      cutoffProductDerivative (derivativeCutoff τ hτ2 i) F Ft t‖ ≤
      α*‖Fit‖ + β*‖Fi‖ + β*‖Ft‖ + γ*‖F‖ := by
  have h1 := cutoff_product_norm τ Fi Fit t α β hα (hβ t)
  have h2 := cutoff_product_norm (derivativeCutoff τ hτ2 i) F Ft t β γ (hβ i) hγ
  exact (norm_add_le _ _).trans (by linarith)

end OQ14.Packet05MixedCutoffSourceBounds
#print axioms OQ14.Packet05MixedCutoffSourceBounds.mixed_cutoff_product_norm

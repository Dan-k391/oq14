import ComplexSphereHelmholtz

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexSphereDivergence
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ComplexResponseTests OQ14.ComplexSphereWeak
  OQ14.ExteriorHelmholtz
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem actual_divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball 0 1) :
    (∑ j : Fin 3, ∫ x, response (ModalWeightedMode.coefficient n hn) z 1 u
      (VectorFourier.coordinateMap x) j * dcoord φ x j) = 0 := by
  let s := CompactSmoothSchwartz.ofCompact φ hφ hc
  let f : Test := ⟨s, hc⟩
  have h := ComplexSphereWeak.divergence_zero n hn z hz u hker f hs
  simpa only [pair, testPair_integral, testPartial, GradientProjection.pderivative_apply,
    CompactSmoothSchwartz.ofCompact_apply, f, dcoord] using h

#print axioms OQ14.ComplexSphereDivergence.actual_divergence
end OQ14.ComplexSphereDivergence

namespace OQ14.ComplexSphereDivergence
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ExteriorHelmholtz OQ14.RadialNormTest
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial
open scoped Topology

theorem radial_test_divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1) (p : Poly) :
    (∑ j : Fin 3, ∫ x, response (ModalWeightedMode.coefficient n hn) z 1 u
      (VectorFourier.coordinateMap x) j *
      (deriv η ‖x‖ * GreenKernel.unitCoordinate j x * complexEvaluate p x +
       η ‖x‖ * dcoord (complexEvaluate p) x j)) = 0 := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.ne' rfl
  have htest : tsupport (test η p) ⊆ ball (0 : Space) 1 := by
    intro x hx
    have h := hs (radialNorm_tsupport η (tsupport_mul_subset_left hx))
    simpa only [mem_ball, dist_zero_right] using h.2
  have h := actual_divergence n hn z hz u hker (test η p) (test_regular η hη h0 p)
    (test_compact η hc p) htest
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ x : Space ∂volume, x ≠ 0 from compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with x hx
  have hreg : DifferentiableAt ℝ (radialNorm η) x :=
    (radialNorm_smooth η hη h0).differentiable (by simp) x
  have hpreg : DifferentiableAt ℝ (complexEvaluate p) x :=
    (complexEvaluate_regular p).differentiable (by simp) x
  rw [show test η p = fun y => radialNorm η y * complexEvaluate p y from rfl,
    partial_mul hreg hpreg, radialNorm_partial η hη x hx j]
  dsimp [radialNorm]
  ring

#print axioms OQ14.ComplexSphereDivergence.radial_test_divergence
end OQ14.ComplexSphereDivergence

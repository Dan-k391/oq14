import ModalAxialDynamic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalAxialIntegrability
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalAxialRotation
  OQ14.ModalWeightedMode
open scoped Topology

def source (n : ℝ) (hn : 1 < n) (θ : ℝ) (u : VectorFourier.VectorL2) (j : Fin 3) : Space → ℂ :=
  fun y => DynamicVolume.source (coefficient n hn) u j (rotation (-θ) y)

theorem source_integrable (n : ℝ) (hn : 1 < n) (θ : ℝ) (u : VectorFourier.VectorL2) (j : Fin 3) :
    Integrable (source n hn θ u j) := by
  have h := DynamicVolume.source_integrable (coefficient n hn) u 1 (coefficient_support n hn) j
  exact ((rotation (-θ)).measurePreserving.integrable_comp h.aestronglyMeasurable).mpr h

theorem source_zero (n : ℝ) (hn : 1 < n) (θ : ℝ) (u : VectorFourier.VectorL2)
    (j : Fin 3) (y : Space) (hy : y ∉ closedBall 0 1) : source n hn θ u j y = 0 := by
  unfold source
  apply DynamicVolume.source_zero (coefficient n hn) u 1 (coefficient_support n hn)
  simpa [mem_closedBall, dist_zero_right, (rotation (-θ)).norm_map] using hy

theorem kernel_source_eq (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorFourier.VectorL2)
    (i j : Fin 3) (x y : Space) (hx : x ∈ closedBall 0 1) :
    DynamicConvolution.kernel k 2 i j (x-y) * source n hn θ u j y =
      DyadicKernel.remainder k (x-y) i j * source n hn θ u j y := by
  by_cases hy : y ∈ closedBall (0 : Space) 1
  · have hxy : x-y ∈ closedBall (0 : Space) 2 := by
      have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
      have h := norm_sub_le x y
      simp only [mem_closedBall, dist_zero_right]
      linarith
    simp [DynamicConvolution.kernel, hxy]
  · rw [source_zero n hn θ u j y hy]
    simp

theorem remainder_integrable_ae (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorFourier.VectorL2)
    (i j : Fin 3) : ∀ᵐ x ∂(volume : Measure Space), x ∈ closedBall 0 1 →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i j * source n hn θ u j y) := by
  have h := (source_integrable n hn θ u j).ae_convolution_exists
    (ContinuousLinearMap.mul ℂ ℂ) (DynamicConvolution.kernel_integrable k 2 i j)
  filter_upwards [h] with x hx hxb
  apply hx.congr
  filter_upwards with y
  change source n hn θ u j y * DynamicConvolution.kernel k 2 i j (x-y) = _
  rw [mul_comm, kernel_source_eq n hn θ k u i j x y hxb]

#print axioms OQ14.ModalAxialIntegrability.remainder_integrable_ae
#print axioms OQ14.ModalAxialIntegrability.source_integrable
#print axioms OQ14.ModalAxialIntegrability.source_zero
end OQ14.ModalAxialIntegrability

import ModalAxialKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalAxialDynamic
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalAxialRotation
  OQ14.ModalWeightedMode OQ14.ModalAxialKernel
open scoped Topology

theorem source_action (n : ℝ) (hn : 1 < n) (θ : ℝ) (u : VectorFourier.VectorL2) (i : Fin 3) :
    DynamicVolume.source (coefficient n hn) (action θ u) i =ᵐ[volume]
      fun y => ∑ j : Fin 3, matrix θ i j * DynamicVolume.source (coefficient n hn) u j (rotation (-θ) y) := by
  filter_upwards [action_ae θ u i] with y hy
  unfold DynamicVolume.source
  rw [hy]
  have hm : (coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) y)) =
      (coefficient n hn).value (VectorFourier.coordinateMap y) := material_invariant n hn (-θ) y
  rw [hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms OQ14.ModalAxialDynamic.source_action
end OQ14.ModalAxialDynamic

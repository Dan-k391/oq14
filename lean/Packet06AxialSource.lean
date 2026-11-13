import Packet06MaterialSymmetry
import ModalAxialKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06AxialSource
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalAxialRotation
  OQ14.ModalAxialKernel OQ14.StaticCoefficient OQ14.Packet06MaterialSymmetry
open scoped Topology

theorem source_action (c : Coefficient) (hc : Axial c) (θ : ℝ) (u : VectorFourier.VectorL2) (i : Fin 3) :
    DynamicVolume.source c (action θ u) i =ᵐ[volume]
      fun y => ∑ j : Fin 3, matrix θ i j * DynamicVolume.source c u j (rotation (-θ) y) := by
  filter_upwards [action_ae θ u i] with y hy
  unfold DynamicVolume.source
  rw [hy, hc (-θ) y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def source (c : Coefficient) (θ : ℝ) (u : VectorFourier.VectorL2) (j : Fin 3) : Maxwell.Space → ℂ :=
  fun y => DynamicVolume.source c u j (rotation (-θ) y)

theorem source_integrable (c : Coefficient) (R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (θ : ℝ) (u : VectorFourier.VectorL2) (j : Fin 3) : Integrable (source c θ u j) := by
  have h := DynamicVolume.source_integrable c u R hc j
  exact ((rotation (-θ)).measurePreserving.integrable_comp h.aestronglyMeasurable).mpr h

theorem source_zero (c : Coefficient) (R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (θ : ℝ) (u : VectorFourier.VectorL2) (j : Fin 3) (y : Maxwell.Space)
    (hy : y ∉ closedBall 0 R) : source c θ u j y = 0 := by
  unfold source
  apply DynamicVolume.source_zero c u R hc
  simpa [mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hy
#print axioms OQ14.Packet06AxialSource.source_action
#print axioms OQ14.Packet06AxialSource.source_integrable
#print axioms OQ14.Packet06AxialSource.source_zero
end OQ14.Packet06AxialSource

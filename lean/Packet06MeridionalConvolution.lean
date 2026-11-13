import Packet06MaterialSymmetry
import ModalMeridionalVolume
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MeridionalConvolution
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalMeridionalReflection
  OQ14.ModalMeridionalStatic OQ14.HalfTurnVectorAction
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem source_action (c : StaticCoefficient.Coefficient) (hc : Packet06MaterialSymmetry.Meridional c)
    (u : VectorL2) (j : Fin 3) :
    (fun y => DynamicVolume.source c (action u) j y) =ᵐ[volume]
      fun y => (sign j : ℂ) * DynamicVolume.source c u j (reflection y) := by
  filter_upwards [ModalMeridionalReflection.action_ae u j] with y hy
  unfold DynamicVolume.source
  rw [hy,hc y]
  ring

theorem weighted_comm (c : StaticCoefficient.Coefficient) (hc : Packet06MaterialSymmetry.Meridional c) (R : ℝ)
    (hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (k : ℝ) (u : VectorL2) :
    action (DynamicVolume.weightedRemainder c k R u) =
      DynamicVolume.weightedRemainder c k R (action u) := by
  let T := DynamicVolume.weightedRemainder c k R
  have hT (u : VectorL2) (i : Fin 3) :
      (fun x => T u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j y :=
    DynamicVolume.weightedRemainder_actual c u k R hsupp i
  have hK (x y : Maxwell.Space) (i j : Fin 3) :
      DyadicKernel.remainder k (reflection x-reflection y) i j =
        (sign i : ℂ)*(sign j : ℂ)*DyadicKernel.remainder k (x-y) i j := by
    rw [← map_sub]; exact ModalMeridionalVolume.remainder_reflect k (x-y) i j
  apply vector_ext_pt
  intro i
  have I1 (x : Maxwell.Space) (j : Fin 3) :
      (∫ y, DyadicKernel.remainder k (reflection x-y) i j * DynamicVolume.source c u j y)=
        (sign i : ℂ)*(sign j : ℂ)*∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have h := hK x (reflection y) i j
    rw [reflection_reflection] at h
    rw [h]; ring
  have I2 (x : Maxwell.Space) (j : Fin 3) :
      (∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c (action u) j y)=
        (sign j : ℂ)*∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y := by
    have h3 : (∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c (action u) j y)=
        ∫ y,(sign j : ℂ)*(DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j (reflection y)) := by
      apply integral_congr_ae
      filter_upwards [source_action c hc u j] with y hy
      rw [hy]; ring
    have h4 := reflection.measurePreserving.integral_comp reflection.toHomeomorph.measurableEmbedding
      (fun y' => DyadicKernel.remainder k (x-reflection y') i j * DynamicVolume.source c u j y')
    simp only [reflection_reflection] at h4
    rw [h3,integral_const_mul]
    congr 1
  filter_upwards [ModalMeridionalReflection.action_ae (T u) i,ae_reflect (hT u i),hT (action u) i] with x h1 h2 h3
  rw [h1,h3,h2,hc x]
  simp only [I1,I2]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := sign_sq i
  linear_combination ((Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*(sign j : ℂ)*
    ∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y)*h

#print axioms OQ14.Packet06MeridionalConvolution.source_action
#print axioms OQ14.Packet06MeridionalConvolution.weighted_comm
end OQ14.Packet06MeridionalConvolution

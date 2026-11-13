import Packet06CyclicPotential

/-! Actual dynamic volume remainder intertwines with cyclic rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicDynamic
open MeasureTheory Metric Packet06CyclicRotation Packet06CyclicL2 Packet06CyclicMaterial
open WeakCurl (previous)

theorem coefficient_support (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    ∀ x : Maxwell.Space, x ∉ closedBall 0 R → (coefficient c).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  rw [coefficient_value]
  apply hc
  intro hu
  apply hx
  have hn : ‖unrotate x‖ = ‖x‖ := by
    have h := rotation.symm.norm_map x
    exact h
  simpa only [mem_closedBall, dist_zero_right, hn] using hu

theorem weightedRemainder_conjugacy (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorFourier.VectorL2) :
    DynamicVolume.weightedRemainder (coefficient c) k R (action u) =
      action (DynamicVolume.weightedRemainder c k R u) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hc' := coefficient_support c R hc
  have hR := DynamicVolume.weightedRemainder_actual (coefficient c) (action u) k R hc' i
  have hL := rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    (DynamicVolume.weightedRemainder_actual c u k R hc (previous i))
  filter_upwards [hR, action_ae (DynamicVolume.weightedRemainder c k R u) i, hL] with x hR hA hL
  rw [hR,hA]
  change (Real.sqrt ((coefficient c).value (VectorFourier.coordinateMap x)) : ℂ) *
      Packet06AxialConvolution.potential (coefficient c) k (action u) x i = _
  change DynamicVolume.weightedRemainder c k R u (VectorFourier.coordinateMap (unrotate x)) (previous i) =
    (Real.sqrt (c.value (VectorFourier.coordinateMap (unrotate x))) : ℂ) *
      Packet06AxialConvolution.potential c k u (unrotate x) (previous i) at hL
  rw [hL,coefficient_value,Packet06CyclicPotential.potential_rotate]

theorem real_volume_conjugacy (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorFourier.VectorL2) :
    DynamicVolume.volumeBlock (coefficient c) k R (action u) =
      action (DynamicVolume.volumeBlock c k R u) := by
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [Packet06CyclicProjection.static_volume_conjugacy, weightedRemainder_conjugacy c k R hc]

end OQ14.Packet06CyclicDynamic
#print axioms OQ14.Packet06CyclicDynamic.coefficient_support
#print axioms OQ14.Packet06CyclicDynamic.weightedRemainder_conjugacy
#print axioms OQ14.Packet06CyclicDynamic.real_volume_conjugacy

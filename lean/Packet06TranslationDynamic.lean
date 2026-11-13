import Packet06TranslationPotential

/-! Actual real-frequency material volume block under a rigid shift. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationDynamic
open MeasureTheory Metric Maxwell Packet06TranslationL2 Packet06TranslationMaterial

theorem weightedRemainder_conjugacy (a : Space) (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorFourier.VectorL2) :
    DynamicVolume.weightedRemainder (coefficient a c) k (R+‖a‖) (action a u) =
      action a (DynamicVolume.weightedRemainder c k R u) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hc' := coefficient_support a c R hc
  have hR := DynamicVolume.weightedRemainder_actual (coefficient a c) (action a u) k (R+‖a‖) hc' i
  have hL := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae
    (DynamicVolume.weightedRemainder_actual c u k R hc i)
  filter_upwards [hR, action_ae a (DynamicVolume.weightedRemainder c k R u) i, hL] with x hR hA hL
  rw [hR,hA]
  change (Real.sqrt ((coefficient a c).value (VectorFourier.coordinateMap x)) : ℂ) *
      Packet06AxialConvolution.potential (coefficient a c) k (action a u) x i = _
  have hL' : DynamicVolume.weightedRemainder c k R u (VectorFourier.coordinateMap (x-a)) i =
    (Real.sqrt (c.value (VectorFourier.coordinateMap (x-a))) : ℂ) *
      Packet06AxialConvolution.potential c k u (x-a) i := by
    simpa only [sub_eq_add_neg] using hL
  rw [hL',coefficient_value,Packet06TranslationPotential.potential_translate]

theorem real_volume_conjugacy (a : Space) (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorFourier.VectorL2) :
    DynamicVolume.volumeBlock (coefficient a c) k (R+‖a‖) (action a u) =
      action a (DynamicVolume.volumeBlock c k R u) := by
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [static_volume_conjugacy, weightedRemainder_conjugacy a c k R hc]

end OQ14.Packet06TranslationDynamic
#print axioms OQ14.Packet06TranslationDynamic.weightedRemainder_conjugacy
#print axioms OQ14.Packet06TranslationDynamic.real_volume_conjugacy

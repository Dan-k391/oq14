import Packet06RadiusIndependence
import ConicalCommonBaseline

/-! Actual L² translation and physical pairing for an arbitrary rigid shift. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationL2
open MeasureTheory Maxwell

def action (a : Space) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i ∘L (StaticBallTranslation.scalar a).toContinuousLinearMap ∘L DynamicConvolution.component i

theorem component_action (a : Space) (i : Fin 3) (u : VectorFourier.VectorL2) :
    DynamicConvolution.component i (action a u) = StaticBallTranslation.scalar a (DynamicConvolution.component i u) := by
  simp only [action, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    DynamicConvolution.component_insert]
  simp

theorem action_ae (a : Space) (u : VectorFourier.VectorL2) (i : Fin 3) :
    (fun x => action a u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => u (VectorFourier.coordinateMap (x-a)) i := by
  have hr := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae
    (HalfTurnVectorAction.component_ae u i)
  filter_upwards [HalfTurnVectorAction.component_ae (action a u) i,
    StaticBallTranslation.scalar_ae a (DynamicConvolution.component i u), hr] with x ha hp hr'
  rw [← ha, component_action, hp]
  simpa only [sub_eq_add_neg] using hr'

theorem vectorPair_invariant (a : Space) (u v : VectorFourier.VectorL2) :
    KernelReciprocity.vectorPair (action a u) (action a v) = KernelReciprocity.vectorPair u v := by
  rw [Packet06PhysicalPairing.vectorPair_physical, Packet06PhysicalPairing.vectorPair_physical]
  have he : (∫ x : Space, ∑ i : Fin 3,
      action a u (VectorFourier.coordinateMap x) i * action a v (VectorFourier.coordinateMap x) i) =
      ∫ x : Space, ∑ i : Fin 3, u (VectorFourier.coordinateMap (x-a)) i * v (VectorFourier.coordinateMap (x-a)) i := by
    apply integral_congr_ae
    filter_upwards [action_ae a u 0,action_ae a u 1,action_ae a u 2,
      action_ae a v 0,action_ae a v 1,action_ae a v 2] with x hu0 hu1 hu2 hv0 hv1 hv2
    simp [Fin.sum_univ_three,hu0,hu1,hu2,hv0,hv1,hv2]
  rw [he]
  have hh := integral_add_right_eq_self (μ := (volume : Measure Space))
    (fun x : Space => ∑ i : Fin 3, u (VectorFourier.coordinateMap (x-a)) i * v (VectorFourier.coordinateMap (x-a)) i) a
  simpa only [add_sub_cancel_right] using hh.symm

end OQ14.Packet06TranslationL2
#print axioms OQ14.Packet06TranslationL2.component_action
#print axioms OQ14.Packet06TranslationL2.action_ae
#print axioms OQ14.Packet06TranslationL2.vectorPair_invariant

import Packet06CyclicPairing

/-! Actual L² action of the proper cyclic Cartesian rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicL2
open MeasureTheory Packet06CyclicRotation
open WeakCurl (previous)

def pullback : FourierL2.ScalarL2 →L[ℂ] FourierL2.ScalarL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rotation.symm : Maxwell.Space → Maxwell.Space)
    rotation.symm.measurePreserving).toContinuousLinearMap

theorem pullback_ae (f : FourierL2.ScalarL2) :
    pullback f =ᵐ[volume] fun x => f (unrotate x) :=
  Lp.coeFn_compMeasurePreserving f rotation.symm.measurePreserving

def action : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i ∘L pullback ∘L DynamicConvolution.component (previous i)

theorem component_action (i : Fin 3) (u : VectorFourier.VectorL2) :
    DynamicConvolution.component i (action u) = pullback (DynamicConvolution.component (previous i) u) := by
  simp only [action, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    DynamicConvolution.component_insert]
  simp

theorem action_ae (u : VectorFourier.VectorL2) (i : Fin 3) :
    (fun x => action u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => u (VectorFourier.coordinateMap (unrotate x)) (previous i) := by
  have hr := rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    (HalfTurnVectorAction.component_ae u (previous i))
  filter_upwards [HalfTurnVectorAction.component_ae (action u) i,
    pullback_ae (DynamicConvolution.component (previous i) u), hr] with x ha hp hr'
  rw [← ha, component_action, hp]
  exact hr'

/-- The constructed L² rotation preserves the physical bilinear pairing. -/
theorem vectorPair_invariant (u v : VectorFourier.VectorL2) :
    KernelReciprocity.vectorPair (action u) (action v) = KernelReciprocity.vectorPair u v :=
  Packet06CyclicPairing.vectorPair_rotation u v (action u) (action v) (action_ae u) (action_ae v)
end OQ14.Packet06CyclicL2
#print axioms OQ14.Packet06CyclicL2.pullback_ae
#print axioms OQ14.Packet06CyclicL2.component_action
#print axioms OQ14.Packet06CyclicL2.action_ae
#print axioms OQ14.Packet06CyclicL2.vectorPair_invariant

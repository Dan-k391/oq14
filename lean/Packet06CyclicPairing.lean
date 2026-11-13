import Packet06CyclicAffine
import Packet06PhysicalPairing

/-! The actual unconjugated physical volume pairing is invariant under the
    proper cyclic Cartesian rotation, given its a.e. L² field action. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicPairing
open MeasureTheory KernelReciprocity Packet06CyclicRotation
open WeakCurl (previous)

theorem vectorPair_rotation (u v ur vr : VectorFourier.VectorL2)
    (hu : ∀ i : Fin 3, (fun x : Maxwell.Space => ur (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => u (VectorFourier.coordinateMap (unrotate x)) (previous i))
    (hv : ∀ i : Fin 3, (fun x : Maxwell.Space => vr (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => v (VectorFourier.coordinateMap (unrotate x)) (previous i)) :
    vectorPair ur vr = vectorPair u v := by
  rw [Packet06PhysicalPairing.vectorPair_physical, Packet06PhysicalPairing.vectorPair_physical]
  have he : (∫ x : Maxwell.Space, ∑ i : Fin 3,
      ur (VectorFourier.coordinateMap x) i * vr (VectorFourier.coordinateMap x) i) =
      ∫ x : Maxwell.Space, ∑ i : Fin 3,
        u (VectorFourier.coordinateMap (unrotate x)) i * v (VectorFourier.coordinateMap (unrotate x)) i := by
    apply integral_congr_ae
    filter_upwards [hu 0,hu 1,hu 2,hv 0,hv 1,hv 2] with x hu0 hu1 hu2 hv0 hv1 hv2
    simp [Fin.sum_univ_three, hu0,hu1,hu2,hv0,hv1,hv2,WeakCurl.previous]
    ring
  rw [he]
  have hh := rotation.symm.measurePreserving.integral_comp rotation.symm.toHomeomorph.measurableEmbedding
    (fun x : Maxwell.Space => ∑ i : Fin 3, u (VectorFourier.coordinateMap x) i * v (VectorFourier.coordinateMap x) i)
  simpa [Function.comp_apply, rotation] using hh

end OQ14.Packet06CyclicPairing
#print axioms OQ14.Packet06CyclicPairing.vectorPair_rotation

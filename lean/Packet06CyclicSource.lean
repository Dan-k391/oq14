import Packet06CyclicProjection

/-! The true compact material source follows the rotated coefficient and L² mode. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicSource
open MeasureTheory Packet06CyclicRotation Packet06CyclicL2 Packet06CyclicMaterial
open WeakCurl (previous)

theorem source_action (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) (i : Fin 3) :
    DynamicVolume.source (coefficient c) (action u) i =ᵐ[volume]
      fun x => DynamicVolume.source c u (previous i) (unrotate x) := by
  filter_upwards [action_ae u i] with x hx
  simp only [DynamicVolume.source, coefficient_value]
  rw [hx]

end OQ14.Packet06CyclicSource
#print axioms OQ14.Packet06CyclicSource.source_action

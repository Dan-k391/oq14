import Packet06RigidStateSector
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSector
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06GenericSectorConjugate Packet06RigidPencilState
theorem embedding_injective {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ} (d : State c₀ R₀)
    (s : ℝ) (hs : 0 < s) (a : Space) : Function.Injective (embedding d s hs a) := by
  intro u v huv
  simp only [embedding,ContinuousLinearMap.comp_apply] at huv
  exact Subtype.ext ((placed s hs a).injective (d.embedding.injective huv))

end OQ14.Packet06RigidStateSector
#print axioms OQ14.Packet06RigidStateSector.embedding_injective

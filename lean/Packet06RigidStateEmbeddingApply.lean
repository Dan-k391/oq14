import Packet06RigidStateEmbedding
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidStateEmbeddingApply
open Maxwell Packet06SectorOperator Packet06PlacedEquivalence Packet06RigidPencilState Packet06RigidStateSector

theorem embedding_apply {c : StaticCoefficient.Coefficient} {R : ℝ} (p : State c R)
    (s : ℝ) (hs : 0 < s) (a : Space) (u : Sector) :
    embedding p s hs a u = p.embedding (Packet06PlacedKernel.placedUnknown s a u) := by
  simp only [embedding,ContinuousLinearMap.comp_apply,placed_apply]
  rfl
end OQ14.Packet06RigidStateEmbeddingApply
#print axioms OQ14.Packet06RigidStateEmbeddingApply.embedding_apply

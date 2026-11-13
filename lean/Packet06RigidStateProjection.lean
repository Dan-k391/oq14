import Packet06RigidSyncDefs
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateProjection
open Maxwell Packet06PlacedKernel Packet06PlacedEquivalence

theorem pencil_affine_embedding {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ}
    (a : Space) (p : Packet06RigidPencilState.State c₀ R₀) (u : VectorFourier.VectorL2) :
    (Packet06RigidPencilState.affine a p).embedding u = placed 1 (by norm_num) a (p.embedding u) := rfl

theorem hotspot_affine_unknown {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space)
    (d : Packet06RigidHotspotState.State N z r M B) :
    (Packet06RigidHotspotState.affine a d).unknown = placedUnknown 1 a d.unknown := rfl

theorem hotspot_cyclic_unknown {N : ℕ} {z : ℂ} {r M B : ℝ}
    (d : Packet06RigidHotspotState.State N z r M B) :
    (Packet06RigidHotspotState.cyclic d).unknown = placedUnknown 1 0 d.unknown := rfl
end OQ14.Packet06RigidStateProjection
#print axioms OQ14.Packet06RigidStateProjection.pencil_affine_embedding
#print axioms OQ14.Packet06RigidStateProjection.hotspot_affine_unknown
#print axioms OQ14.Packet06RigidStateProjection.hotspot_cyclic_unknown

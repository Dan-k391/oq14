import Packet06RigidStateProjection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSync
open Maxwell Packet06PlacedKernel Packet06PlacedEquivalence
theorem cyclic_sync {N : ℕ} {z : ℂ} {r M B : ℝ} {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ}
    (u : VectorFourier.VectorL2) (p : Packet06RigidPencilState.State c₀ R₀)
    (d : Packet06RigidHotspotState.State N z r M B) (h : Matches u p d) :
    Matches u (Packet06RigidPencilState.affine 0 p) (Packet06RigidHotspotState.cyclic d) := by
  obtain ⟨hm,hr,hu⟩ := h
  refine ⟨?_,?_,?_⟩
  · change placedCoefficient 1 0 p.material = placedCoefficient 1 0 d.material
    rw [hm]
  · change p.radius+‖(0 : Space)‖ = d.supportRadius
    simpa using hr
  · rw [Packet06RigidStateProjection.pencil_affine_embedding,
      Packet06RigidStateProjection.hotspot_cyclic_unknown,placed_apply,hu]

end OQ14.Packet06RigidStateSync
#print axioms OQ14.Packet06RigidStateSync.cyclic_sync

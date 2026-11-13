import Packet06RigidSyncDefs
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSync
open Maxwell Packet06PlacedKernel Packet06PlacedEquivalence
theorem axial_sync {N : ℕ} {z : ℂ} {r M B : ℝ} {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ}
    (u : VectorFourier.VectorL2) (p : Packet06RigidPencilState.State c₀ R₀)
    (d : Packet06RigidHotspotState.State N z r M B) (h : Matches u p d) (θ : ℝ) :
    Matches u (Packet06RigidPencilState.axial θ p) (Packet06RigidHotspotState.axial θ d) := by
  obtain ⟨hm,hr,hu⟩ := h
  refine ⟨?_,?_,?_⟩
  · change Packet06AxialMaterialTransport.coefficient θ p.material = Packet06AxialMaterialTransport.coefficient θ d.material
    rw [hm]
  · change p.radius = d.supportRadius
    exact hr
  · change ModalAxialRotation.action θ (p.embedding u) = ModalAxialRotation.action θ d.unknown
    rw [hu]


end OQ14.Packet06RigidStateSync
#print axioms OQ14.Packet06RigidStateSync.axial_sync

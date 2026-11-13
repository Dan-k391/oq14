import Packet06RigidSyncAxial
import Packet06RigidSyncAffine
import Packet06RigidSyncCyclic

/-! The actual frame hotspot state and the full spectral frame are the
same material, support radius, and physical mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSync
open Maxwell Packet06RigidPencilState Packet06FullFrameObservedPole

theorem full_sync {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : Packet06RigidHotspotState.State N z r M B) :
    Matches d.unknown (full θ φ a (initial d.material d.supportRadius d.support_nonnegative d.support))
      (Packet06RigidHotspotFrame.transform θ φ a d) := by
  unfold full Packet06RigidHotspotFrame.transform
  apply affine_sync
  apply cyclic_sync
  apply cyclic_sync
  apply axial_sync
  apply cyclic_sync
  apply cyclic_sync
  apply axial_sync
  apply cyclic_sync
  exact ⟨rfl,rfl,rfl⟩
end OQ14.Packet06RigidStateSync
#print axioms OQ14.Packet06RigidStateSync.full_sync

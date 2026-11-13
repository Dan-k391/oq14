import Packet06FullFrameObservedPole
import Packet06RigidHotspotFrame

/-! The spectral pencil state and the physical hotspot state track the
same material, support radius, and transformed mode at every frame step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06RigidStateSync
open Maxwell Packet06PlacedKernel Packet06PlacedEquivalence

 def Matches {N : ℕ} {z : ℂ} {r M B : ℝ} {c₀ : StaticCoefficient.Coefficient} {R₀ : ℝ}
    (u : VectorFourier.VectorL2) (p : Packet06RigidPencilState.State c₀ R₀)
    (d : Packet06RigidHotspotState.State N z r M B) : Prop :=
  p.material=d.material ∧ p.radius=d.supportRadius ∧ p.embedding u=d.unknown

end OQ14.Packet06RigidStateSync

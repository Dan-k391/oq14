import Packet06RigidCollarFrame
import Packet06OutgoingMode

/-! Each rigidly transported state remains a genuine global unit-normalized
outgoing Maxwell mode. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidStateOutgoing
open Maxwell Packet06RigidHotspotState Packet06PhysicalNormalization

theorem actual_outgoing {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) :
    Packet06OutgoingMode.IsActualOutgoingMode d.material z d.supportRadius d.unknown := by
  have hne : d.unknown ≠ 0 := by
    intro h
    have hn := d.normalization
    rw [h] at hn
    simp [reciprocalNorm,KernelReciprocity.vectorPair,KernelReciprocity.scalarPair] at hn
  exact Packet06OutgoingMode.actual_outgoing_mode d.material z d.supportRadius d.support_nonnegative
    d.unknown d.support d.kernel hne

end OQ14.Packet06RigidStateOutgoing
#print axioms OQ14.Packet06RigidStateOutgoing.actual_outgoing

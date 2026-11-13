import Packet06NeighborhoodTraceIntrinsic
import Packet06NeighborhoodWeightedBall

/-! The transported maximum is independent of every alternate actual
one-sided representative on the same strictly larger ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet06StrongFrameIntrinsic
open Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet06PhaseWeightedMaximum
  Packet06NeighborhoodWeighted Packet06NeighborhoodWeightedFrame Packet06RigidHotspotState
abbrev Space := Maxwell.Space

theorem intrinsic {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space) (d : State N z r M B)
    (i : Fin N) (R n η : ℝ) (hr : r < R) (inside outside inside' outside' : Fin 3 → Space → ℂ)
    (b : Bool) (x : Space)
    (h : Certificate (Packet06RigidHotspotFrame.transform θ φ a d) i
      (sets θ φ a (closedBall (d.center i) R)) n η inside outside b x)
    (h' : Trace (Packet06RigidHotspotFrame.transform θ φ a d).material z
      (Packet06RigidHotspotFrame.transform θ φ a d).unknown (Packet06RigidHotspotFrame.transform θ φ a d).body
      (closedBall ((Packet06RigidHotspotFrame.transform θ φ a d).center i) R) inside' outside') :
    (∀ p j y, y ∈ closedBall ((Packet06RigidHotspotFrame.transform θ φ a d).center i) r ∩
      phaseDomain (Packet06RigidHotspotFrame.transform θ φ a d).body p →
      phaseField inside outside p j y = phaseField inside' outside' p j y) ∧
    (∀ p y, y ∈ closedBall ((Packet06RigidHotspotFrame.transform θ φ a d).center i) r ∩
      phaseDomain (Packet06RigidHotspotFrame.transform θ φ a d).body p →
      phasePermittivity n η p * (physicalAmplitude (phaseField inside outside p) y)^2 =
        phasePermittivity n η p * (physicalAmplitude (phaseField inside' outside' p) y)^2) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside' outside' b) x)^2 ∧
    (∀ p y, y ∈ closedBall ((Packet06RigidHotspotFrame.transform θ φ a d).center i) r ∩
      phaseDomain (Packet06RigidHotspotFrame.transform θ φ a d).body p →
      phasePermittivity n η p * (physicalAmplitude (phaseField inside' outside' p) y)^2 ≤
        phasePermittivity n η b * (physicalAmplitude (phaseField inside' outside' b) x)^2) := by
  rw [sets_eq_image,Packet07DrivenRigidGeometry.placement_ball] at h
  have hc : Packet07DrivenRigidHotspot.placement θ φ a (d.center i) =
      (Packet06RigidHotspotFrame.transform θ φ a d).center i :=
    (Packet06RigidHotspotFrame.frame_center θ φ a d i).symm
  rw [hc] at h
  exact Packet06NeighborhoodTraceIntrinsic.intrinsic _ i R n η hr inside outside inside' outside' b x h h'
end OQ14.Packet06StrongFrameIntrinsic
#print axioms OQ14.Packet06StrongFrameIntrinsic.intrinsic

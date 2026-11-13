import Packet06NeighborhoodWeightedFrame
import Packet07DrivenRigidGeometry

/-! The larger closed ball remains strictly larger under the full rigid frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06NeighborhoodWeightedBall
open Set Metric Maxwell Packet06RigidHotspotState Packet06NeighborhoodWeighted
  Packet06NeighborhoodWeightedFrame Packet06PhaseWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum
abbrev Space := Maxwell.Space

theorem frame_ball {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space) (d : State N z r M B)
    (i : Fin N) (R n η : ℝ) (hR : r < R) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (h : Certificate d i (closedBall (d.center i) R) n η inside outside b x) :
    r < R ∧ Certificate (Packet06RigidHotspotFrame.transform θ φ a d) i
      (closedBall ((Packet06RigidHotspotFrame.transform θ φ a d).center i) R) n η
      (branches θ φ a inside) (branches θ φ a outside) b (Packet07DrivenRigidHotspot.placement θ φ a x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (branches θ φ a inside)
      (branches θ φ a outside) b) (Packet07DrivenRigidHotspot.placement θ φ a x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  have hh := frame θ φ a d i (closedBall (d.center i) R) n η inside outside b x h
  rw [sets_eq_image,Packet07DrivenRigidGeometry.placement_ball] at hh
  have hc : Packet07DrivenRigidHotspot.placement θ φ a (d.center i) = (Packet06RigidHotspotFrame.transform θ φ a d).center i := by
    exact (Packet06RigidHotspotFrame.frame_center θ φ a d i).symm
  rw [hc] at hh
  exact ⟨hR,hh⟩
end OQ14.Packet06NeighborhoodWeightedBall
#print axioms OQ14.Packet06NeighborhoodWeightedBall.frame_ball

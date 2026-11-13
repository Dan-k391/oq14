import Packet06RigidMaterialValues
import Packet06PhaseWeightedMaximum
import Packet07DrivenRigidGeometry

/-! The rotated observation balls retain their actual open-phase dielectric values.
At an interface, phasePermittivity remains a one-sided trace convention. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06RigidPhasePermittivity
open Set Metric Maxwell Packet06RigidHotspotState Packet06RigidHotspotFrame
  Packet06RigidMaterialValues Packet06PhaseWeightedMaximum Packet07DrivenRigidHotspot
abbrev Space := Maxwell.Space

theorem phase_ball_image {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (i : Fin N) :
    placement θ φ a '' closedBall (d.center i) r =
      closedBall ((transform θ φ a d).center i) r := by
  rw [Packet07DrivenRigidGeometry.placement_ball,frame_center]
  rfl

theorem same_side_values {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (outer : Set Space) (n η : ℝ)
    (hlaw : ∀ x, MaterialMaxwell.dielectric d.material x =
      (by classical exact if x ∈ d.body then (1+η)*n^2 else if x ∈ outer then n^2 else 1))
    (hhost : ∀ i, closedBall (d.center i) r ⊆ outer) :
    ∀ i y, y ∈ closedBall ((transform θ φ a d).center i) r →
      (y ∈ (transform θ φ a d).body →
        MaterialMaxwell.dielectric (transform θ φ a d).material y = phasePermittivity n η true) ∧
      (y ∉ closure ((transform θ φ a d).body) →
        MaterialMaxwell.dielectric (transform θ φ a d).material y = phasePermittivity n η false) := by
  classical
  intro i y hy
  rw [←phase_ball_image θ φ a d i] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  have hb : (transform θ φ a d).body = placement θ φ a '' d.body := by
    rw [frame_body]
    rfl
  have hv := frame_value θ φ a d x
  change MaterialMaxwell.dielectric (transform θ φ a d).material (placement θ φ a x) = _ at hv
  have he : placement θ φ a x ∈ (transform θ φ a d).body ↔ x ∈ d.body := by
    rw [hb]
    exact (placement θ φ a).injective.mem_set_image
  refine ⟨?_,?_⟩
  · intro hin
    rw [hv,hlaw]
    simp [he.mp hin,phasePermittivity]
  · intro hout
    have hnot : x ∉ d.body := by
      intro hxbody
      exact hout (subset_closure (he.mpr hxbody))
    rw [hv,hlaw]
    simp [hnot,hhost i hx,phasePermittivity]

/-- Both weights are continuous on their own closed trace domain.  This does not
identify their distinct values at an interface point. -/
theorem trace_weights_continuous {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (n η : ℝ) (i : Fin N) (b : Bool) :
    ContinuousOn (fun _ : Space => phasePermittivity n η b)
      (closedBall ((transform θ φ a d).center i) r ∩
        Packet05BinaryPhaseMaximum.phaseDomain ((transform θ φ a d).body) b) := continuousOn_const
end OQ14.Packet06RigidPhasePermittivity
#print axioms OQ14.Packet06RigidPhasePermittivity.phase_ball_image
#print axioms OQ14.Packet06RigidPhasePermittivity.same_side_values
#print axioms OQ14.Packet06RigidPhasePermittivity.trace_weights_continuous

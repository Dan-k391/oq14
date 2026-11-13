import Packet06RigidFrameGeometry
import Packet07DrivenRigidGeometry

/-! Exact closed-ball geometry under the arbitrary-plane rigid frame. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidClosedGeometry
open Set Metric Maxwell Packet06RigidHotspotState Packet06RigidHotspotFrame Packet07PlaneFrame
  Packet07PlaneCoordinates Packet07PlanarCenters Packet06RigidFrameGeometry
abbrev Space := Maxwell.Space

theorem transformed_closed_geometry {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (O : Set Space)
    (hcenter : ∀ i, (d.center i) 2=0 ∧
      Packet06PlanarProjection.project (d.center i) ∈ (embed θ φ a ⁻¹' O))
    (hproject : ∀ i y, y ∈ closedBall (d.center i) r →
      Packet06PlanarProjection.project y ∈ (embed θ φ a ⁻¹' O))
    (hinj : Function.Injective d.center)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (closedBall (d.center i) r) (closedBall (d.center j) r)) :
    (∀ i, (transform θ φ a d).center i ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O) ∧
    Function.Injective (transform θ φ a d).center ∧
    (∀ i y, y ∈ closedBall ((transform θ φ a d).center i) r → projection θ φ a y ∈ O) ∧
    ∀ i j, i ≠ j → Disjoint (closedBall ((transform θ φ a d).center i) r) (closedBall ((transform θ φ a d).center j) r) := by
  have hopen := transformed_geometry θ φ a d O hcenter
    (fun i y hy => hproject i y (ball_subset_closedBall hy)) hinj
    (fun i j hij => (hdisjoint i j hij).mono ball_subset_closedBall ball_subset_closedBall)
  refine ⟨hopen.1,hopen.2.1,?_,?_⟩
  · intro i y hy
    rw [frame_center] at hy
    change y ∈ closedBall (Packet07DrivenRigidHotspot.placement θ φ a (d.center i)) r at hy
    rw [← Packet07DrivenRigidGeometry.placement_ball θ φ a (d.center i) r] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [Packet07DrivenRigidGeometry.placement_projection]
    exact hproject i x hx
  · intro i j hij
    rw [frame_center,frame_center]
    change Disjoint (closedBall (Packet07DrivenRigidHotspot.placement θ φ a (d.center i)) r) (closedBall (Packet07DrivenRigidHotspot.placement θ φ a (d.center j)) r)
    rw [← Packet07DrivenRigidGeometry.placement_ball θ φ a (d.center i) r,
      ← Packet07DrivenRigidGeometry.placement_ball θ φ a (d.center j) r]
    exact Set.disjoint_image_of_injective (Packet07DrivenRigidHotspot.placement θ φ a).injective (hdisjoint i j hij)
end OQ14.Packet06RigidClosedGeometry
#print axioms OQ14.Packet06RigidClosedGeometry.transformed_closed_geometry

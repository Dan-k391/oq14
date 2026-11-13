import Packet07DrivenRigidHotspot

/-! Rigid placement preserves distances, closed peak balls, and planar projections. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenRigidGeometry
open Set Metric Packet07DrivenRigidHotspot Packet07PlaneCoordinates Packet07PlaneFrame

theorem placement_dist (θ φ : ℝ) (a x y : Maxwell.Space) :
    dist (placement θ φ a x) (placement θ φ a y)=dist x y := by
  rw [dist_eq_norm,dist_eq_norm]
  change ‖(a+normalRotation θ φ x)-(a+normalRotation θ φ y)‖=‖x-y‖
  rw [show (a+normalRotation θ φ x)-(a+normalRotation θ φ y) = normalRotation θ φ (x-y) by simp]
  exact (normalRotation θ φ).norm_map _

theorem placement_ball (θ φ : ℝ) (a c : Maxwell.Space) (r : ℝ) :
    placement θ φ a '' closedBall c r = closedBall (placement θ φ a c) r := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa only [mem_closedBall,placement_dist] using hx
  · intro hy
    refine ⟨(placement θ φ a).symm y,?_,(placement θ φ a).apply_symm_apply y⟩
    rw [mem_closedBall,← placement_dist θ φ a]
    simpa only [Homeomorph.apply_symm_apply] using hy

theorem placement_projection (θ φ : ℝ) (a x : Maxwell.Space) :
    projection θ φ a (placement θ φ a x) = embed θ φ a (Packet07PlanarCenters.planeProject x) := by
  simp [projection,coordinates,placement]
end OQ14.Packet07DrivenRigidGeometry
#print axioms OQ14.Packet07DrivenRigidGeometry.placement_dist
#print axioms OQ14.Packet07DrivenRigidGeometry.placement_ball
#print axioms OQ14.Packet07DrivenRigidGeometry.placement_projection

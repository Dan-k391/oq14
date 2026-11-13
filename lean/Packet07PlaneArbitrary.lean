import Packet07PlanePatch

/-! Full literal arbitrary-plane frame and relatively open patch parameterization. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07PlaneArbitrary
open Set Metric Maxwell Packet07PlaneFrame Packet07PlaneCoordinates Packet07PlanePatch
abbrev Space := Maxwell.Space
abbrev Plane := Packet07PlanarCenters.Plane

theorem arbitrary_plane_patch (n a : Space) (hn : ‖n‖=1) (O : Set Space) (hO : IsOpen O)
    (hne : (affinePlane n a ∩ O).Nonempty) :
    ∃ θ φ : ℝ, ∃ P : Set Plane,
      normalRotation θ φ (EuclideanSpace.single 2 1)=n ∧ IsOpen P ∧ P.Nonempty ∧
      embed θ φ a '' P = affinePlane n a ∩ O ∧
      (∀ u v, dist (embed θ φ a u) (embed θ φ a v)=dist u v) ∧
      (∀ x, projection θ φ a x ∈ affinePlane n a) ∧
      (∀ x ∈ affinePlane n a, projection θ φ a x=x) ∧
      (∀ x y, dist (projection θ φ a x) (projection θ φ a y) ≤ dist x y) ∧
      (∀ x z, z ∈ affinePlane n a → @inner ℝ Space _ (x-projection θ φ a x) (z-a)=0) := by
  obtain ⟨θ,φ,hframe⟩ := exists_frame n hn
  have hne' : (affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O).Nonempty := by
    rw [hframe]
    exact hne
  obtain ⟨hopen,hpn,himage⟩ := patch_pullback θ φ a O hO hne'
  refine ⟨θ,φ,embed θ φ a ⁻¹' O,hframe,hopen,hpn,?_,embed_dist θ φ a,?_,?_,projection_dist_le θ φ a,?_⟩
  · simpa only [hframe] using himage
  · intro x
    rw [←hframe]
    exact embed_plane θ φ a _
  · intro x hx
    apply projection_fixed θ φ a x
    simpa only [hframe] using hx
  · intro x z hz
    apply projection_orthogonal θ φ a x z
    simpa only [hframe] using hz
end OQ14.Packet07PlaneArbitrary
#print axioms OQ14.Packet07PlaneArbitrary.arbitrary_plane_patch

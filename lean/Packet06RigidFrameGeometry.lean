import Packet06RigidMaterialValues
import Packet07PlanePatch

/-! Plane, projection and ball geometry for the exact transported hotspot state. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06RigidFrameGeometry
open Set Metric Maxwell Packet06RigidHotspotState Packet06RigidHotspotFrame Packet07PlaneFrame
  Packet07PlaneCoordinates Packet07PlanarCenters
abbrev Space := Maxwell.Space
abbrev Plane := Packet07PlanarCenters.Plane

theorem frame_projection (θ φ : ℝ) (a y : Space) :
    projection θ φ a (a + normalRotation θ φ y) = embed θ φ a (planeProject y) := by
  simp [projection,coordinates,embed]

theorem plane_image (θ φ : ℝ) (a : Space) :
    (fun x => a + normalRotation θ φ x) '' {x : Space | x 2=0} =
      affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x 2=0 at hx
    have he : planeEmbed (planeProject x)=x := by
      ext i
      fin_cases i <;> simp [planeEmbed,planeProject,hx]
    rw [← he]
    exact embed_plane θ φ a (planeProject x)
  · intro hy
    let x := (normalRotation θ φ).symm (y-a)
    have hx : x 2=0 := by
      have hh : @inner ℝ Space _ x (EuclideanSpace.single 2 1)=0 := by
        rw [← (normalRotation θ φ).inner_map_map x (EuclideanSpace.single 2 1)]
        simpa only [x,LinearIsometryEquiv.apply_symm_apply] using hy
      simpa [EuclideanSpace.inner_single_right] using hh
    exact ⟨x,hx,by simp [x]⟩

theorem frame_balls (θ φ : ℝ) (a c : Space) (r : ℝ) :
    (fun x => a + normalRotation θ φ x) '' ball c r = ball (a + normalRotation θ φ c) r := by
  let h : Space ≃ₜ Space := (normalRotation θ φ).toHomeomorph.trans (Homeomorph.addLeft a)
  ext y
  change y ∈ h '' ball c r ↔ _
  rw [h.image_eq_preimage]
  change dist (h.symm y) c < r ↔ dist y (a + normalRotation θ φ c) < r
  have he : dist (h.symm y) c = dist y (a + normalRotation θ φ c) := by
    have hb : h.symm y = (normalRotation θ φ).symm (y-a) := by
      change (normalRotation θ φ).symm (-a+y) = _
      congr 1
      abel
    rw [hb]
    rw [← (normalRotation θ φ).dist_map ((normalRotation θ φ).symm (y-a)) c,
      LinearIsometryEquiv.apply_symm_apply]
    simp [dist_eq_norm,show y-a-normalRotation θ φ c = y-(a+normalRotation θ φ c) by abel]
  rw [he]

theorem transformed_geometry {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (O : Set Space)
    (hcenter : ∀ i, (d.center i) 2=0 ∧
      Packet06PlanarProjection.project (d.center i) ∈ (embed θ φ a ⁻¹' O))
    (hproject : ∀ i y, y ∈ ball (d.center i) r →
      Packet06PlanarProjection.project y ∈ (embed θ φ a ⁻¹' O))
    (hinj : Function.Injective d.center)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (ball (d.center i) r) (ball (d.center j) r)) :
    (∀ i, (transform θ φ a d).center i ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O) ∧
    Function.Injective (transform θ φ a d).center ∧
    (∀ i y, y ∈ ball ((transform θ φ a d).center i) r → projection θ φ a y ∈ O) ∧
    ∀ i j, i ≠ j → Disjoint (ball ((transform θ φ a d).center i) r) (ball ((transform θ φ a d).center j) r) := by
  have hproj (x : Space) : Packet06PlanarProjection.project x = planeProject x := rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [frame_center]
    have hi := hcenter i
    have he : planeEmbed (planeProject (d.center i)) = d.center i := by
      ext k
      fin_cases k <;> simp [planeEmbed,planeProject,hi.1]
    constructor
    · rw [← he]
      exact embed_plane θ φ a _
    · rw [← he]
      exact hi.2
  · intro i j hij
    rw [frame_center,frame_center] at hij
    apply hinj
    apply (normalRotation θ φ).injective
    exact add_left_cancel hij
  · intro i y hy
    rw [frame_center,← frame_balls θ φ a (d.center i) r] at hy
    obtain ⟨x,hx,rfl⟩ := hy
    rw [frame_projection]
    simpa only [← hproj] using hproject i x hx
  · intro i j hij
    rw [frame_center,frame_center,← frame_balls θ φ a (d.center i) r,
      ← frame_balls θ φ a (d.center j) r]
    exact Set.disjoint_image_of_injective
      (fun x y hxy => (normalRotation θ φ).injective (add_left_cancel hxy)) (hdisjoint i j hij)

end OQ14.Packet06RigidFrameGeometry
#print axioms OQ14.Packet06RigidFrameGeometry.frame_projection
#print axioms OQ14.Packet06RigidFrameGeometry.plane_image
#print axioms OQ14.Packet06RigidFrameGeometry.frame_balls
#print axioms OQ14.Packet06RigidFrameGeometry.transformed_geometry

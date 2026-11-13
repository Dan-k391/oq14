import Packet07PlaneFrame
import Packet07PlanarCenters

/-! Literal affine-plane coordinates and orthogonal projection in any unit-normal frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07PlaneCoordinates
open Maxwell Packet07PlaneFrame Packet07PlanarCenters
abbrev Space := Maxwell.Space
abbrev Plane := Packet07PlanarCenters.Plane

def affinePlane (n a : Space) : Set Space := {x | @inner ℝ Space _ (x-a) n = 0}
def embed (θ φ : ℝ) (a : Space) (u : Plane) : Space := a + normalRotation θ φ (planeEmbed u)
def coordinates (θ φ : ℝ) (a x : Space) : Plane := planeProject ((normalRotation θ φ).symm (x-a))
def projection (θ φ : ℝ) (a x : Space) : Space := embed θ φ a (coordinates θ φ a x)

theorem embed_plane (θ φ : ℝ) (a : Space) (u : Plane) :
    embed θ φ a u ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a := by
  change @inner ℝ Space _ (a+normalRotation θ φ (planeEmbed u)-a)
    (normalRotation θ φ (EuclideanSpace.single 2 1))=0
  rw [add_sub_cancel_left, (normalRotation θ φ).inner_map_map]
  simp [EuclideanSpace.inner_single_right,planeEmbed_coord]

theorem coordinates_embed (θ φ : ℝ) (a : Space) (u : Plane) :
    coordinates θ φ a (embed θ φ a u)=u := by
  simp [coordinates,embed,planeProject_embed]

theorem embed_coordinates (θ φ : ℝ) (a x : Space)
    (hx : x ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a) :
    embed θ φ a (coordinates θ φ a x)=x := by
  let y := (normalRotation θ φ).symm (x-a)
  have hy2 : y 2=0 := by
    have hh : @inner ℝ Space _ y (EuclideanSpace.single 2 1)=0 := by
      rw [← (normalRotation θ φ).inner_map_map y (EuclideanSpace.single 2 1)]
      change @inner ℝ Space _ (x-a) (normalRotation θ φ (EuclideanSpace.single 2 1))=0 at hx
      simpa only [y,LinearIsometryEquiv.apply_symm_apply] using hx
    simpa [EuclideanSpace.inner_single_right] using hh
  have he : planeEmbed (planeProject y)=y := by
    ext i
    fin_cases i <;> simp [planeEmbed,planeProject,hy2]
  change a+normalRotation θ φ (planeEmbed (planeProject y))=x
  rw [he]
  simp [y]

theorem embed_injective (θ φ : ℝ) (a : Space) : Function.Injective (embed θ φ a) := by
  intro u v h
  have hh := congrArg (coordinates θ φ a) h
  simpa only [coordinates_embed] using hh

theorem embed_dist (θ φ : ℝ) (a : Space) (u v : Plane) :
    dist (embed θ φ a u) (embed θ φ a v)=dist u v := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : embed θ φ a u-embed θ φ a v=normalRotation θ φ (planeEmbed u-planeEmbed v) := by
    simp only [embed,map_sub]
    abel
  rw [he,(normalRotation θ φ).norm_map]
  have hn : ‖planeEmbed u-planeEmbed v‖=‖u-v‖ := by
    have h : ‖planeEmbed u-planeEmbed v‖^2=‖u-v‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
      simp [Fin.sum_univ_three,Fin.sum_univ_two,planeEmbed,PiLp.sub_apply]
    nlinarith [norm_nonneg (planeEmbed u-planeEmbed v),norm_nonneg (u-v)]
  exact hn

theorem coordinates_dist_le (θ φ : ℝ) (a x y : Space) :
    dist (coordinates θ φ a x) (coordinates θ φ a y) ≤ dist x y := by
  apply (planeProject_dist_le _ _).trans
  rw [dist_eq_norm,dist_eq_norm,← map_sub,(normalRotation θ φ).symm.norm_map]
  have he : (x-a)-(y-a)=x-y := by abel
  rw [he]

theorem projection_fixed (θ φ : ℝ) (a x : Space)
    (hx : x ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a) : projection θ φ a x=x :=
  embed_coordinates θ φ a x hx

theorem projection_dist_le (θ φ : ℝ) (a x y : Space) :
    dist (projection θ φ a x) (projection θ φ a y) ≤ dist x y := by
  rw [projection,projection,embed_dist]
  exact coordinates_dist_le θ φ a x y
end OQ14.Packet07PlaneCoordinates
#print axioms OQ14.Packet07PlaneCoordinates.embed_plane
#print axioms OQ14.Packet07PlaneCoordinates.coordinates_embed
#print axioms OQ14.Packet07PlaneCoordinates.embed_coordinates
#print axioms OQ14.Packet07PlaneCoordinates.embed_injective
#print axioms OQ14.Packet07PlaneCoordinates.embed_dist
#print axioms OQ14.Packet07PlaneCoordinates.coordinates_dist_le
#print axioms OQ14.Packet07PlaneCoordinates.projection_fixed
#print axioms OQ14.Packet07PlaneCoordinates.projection_dist_le

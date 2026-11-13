import Packet07PlaneArbitrary
import Packet07DrivenFrameHotspot
import Packet07DrivenUniformAffineHotspot

/-! Rigid frame-and-offset placement preserves the literal isolated hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenRigidHotspot
open Set Metric Maxwell Packet07PlaneFrame Packet07PlaneCoordinates Packet07DrivenFrameMaxwell
  Packet07DrivenUniformHotspot Packet07DrivenUniformAffineGeometry
abbrev Space := Maxwell.Space

def placement (θ φ : ℝ) (a : Space) : Space ≃ₜ Space where
  toFun x := a+normalRotation θ φ x
  invFun x := (normalRotation θ φ).symm (x-a)
  left_inv := by intro x; simp
  right_inv := by intro x; simp
  continuous_toFun := continuous_const.add (normalRotation θ φ).continuous
  continuous_invFun := (normalRotation θ φ).symm.continuous.comp (continuous_id.sub continuous_const)

def field (θ φ : ℝ) (a : Space) (E : Field) : Field := fun x => frameField θ φ E (x-a)

theorem placement_embed (θ φ : ℝ) (a : Space) (u : Packet07PlanarCenters.Plane) :
    placement θ φ a (Packet07PlanarCenters.planeEmbed u)=embed θ φ a u := rfl

theorem placement_image (θ φ : ℝ) (a : Space) (S : Set Space) :
    placement θ φ a '' S = (Packet07DrivenUniformAffineGeometry.placement 1 (by norm_num) a) '' (normalRotation θ φ '' S) := by
  ext x
  simp only [mem_image,exists_exists_and_eq_and]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y,hy,by simp [placement,Packet07DrivenUniformAffineGeometry.placement,Packet07AffineGeometry.place,add_comm]⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,hy,by simpa [placement,Packet07DrivenUniformAffineGeometry.placement,Packet07AffineGeometry.place,add_comm] using hxy⟩

theorem rigid_hotspot (θ φ : ℝ) (a : Space) (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (field θ φ a E) (placement θ φ a '' body) (placement θ φ a center) r M B := by
  have hframe := Packet07DrivenFrameHotspot.frame_hotspot θ φ E body hb center r M B hhot
  have hopen := (normalRotation θ φ).toHomeomorph.isOpenMap _ hb
  have hh := Packet07DrivenUniformAffineHotspot.affine_actual_hotspot (frameField θ φ E)
    (normalRotation θ φ '' body) hopen (normalRotation θ φ center) r M B hframe 1 (by norm_num) a
  rw [← placement_image θ φ a body] at hh
  have hfield : Packet07AffineMaxwell.affineField 1 a (frameField θ φ E) = field θ φ a E := by
    funext x i
    simp [Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField,field]
  rw [hfield] at hh
  simpa [field,Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField,
    Packet07DrivenUniformAffineGeometry.placement,Packet07AffineGeometry.place,placement,add_comm,Pi.smul_apply] using hh
end OQ14.Packet07DrivenRigidHotspot
#print axioms OQ14.Packet07DrivenRigidHotspot.placement_embed
#print axioms OQ14.Packet07DrivenRigidHotspot.placement_image
#print axioms OQ14.Packet07DrivenRigidHotspot.rigid_hotspot

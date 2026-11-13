import Packet07DrivenAxialHotspot
import Packet07DrivenCyclicHotspot
import Packet07DrivenFrameMaxwell

/-! The exact normal-reaching frame preserves the actual driven hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenFrameHotspot
open Set Metric Maxwell Packet07DrivenUniformHotspot Packet06CyclicRotation
  Packet06CyclicRotationMaxwell Packet07DrivenInverseCyclic Packet07DrivenFrameMaxwell
abbrev Space := Maxwell.Space

theorem cyclic_hotspot (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (rotateField E) (rotation '' body) (rotation center) r M B := by
  simpa [Packet06PlacementHomeomorph.placement,Packet06PhysicalPlacement.point,rotation] using
    Packet07DrivenCyclicHotspot.cyclic_hotspot E body hb center r M B hhot

theorem rotate_twice (x : Space) : rotate (rotate x)=unrotate x := by
  ext i
  fin_cases i <;> simp [rotate,unrotate,WeakCurl.previous,WeakCurl.next]

theorem inverse_hotspot (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (inverseField E) (rotation.symm '' body) (rotation.symm center) r M B := by
  have h1 := cyclic_hotspot E body hb center r M B hhot
  have h2 := cyclic_hotspot (rotateField E) (rotation '' body) (rotation.toHomeomorph.isOpenMap _ hb)
    (rotation center) r M B h1
  rw [twice_field,Set.image_image] at h2
  have he : (fun x : Space => rotation (rotation x)) = rotation.symm := by
    funext x
    exact rotate_twice x
  rw [he] at h2
  have hc : rotation (rotation center) = rotation.symm center := rotate_twice center
  rwa [hc] at h2

theorem frame_hotspot (θ φ : ℝ) (E : Field) (body : Set Space) (hb : IsOpen body)
    (center : Space) (r M B : ℝ) (hhot : HotspotAbove E body center r M B) :
    HotspotAbove (frameField θ φ E) ((Packet07PlaneFrame.normalRotation θ φ) '' body)
      (Packet07PlaneFrame.normalRotation θ φ center) r M B := by
  have h1 := cyclic_hotspot E body hb center r M B hhot
  have hb1 := rotation.toHomeomorph.isOpenMap _ hb
  have h2 := Packet07DrivenAxialHotspot.rotate_hotspot φ (rotateField E) (rotation '' body) hb1
    (rotation center) r M B h1
  have hb2 := (ModalAxialRotation.rotation φ).toHomeomorph.isOpenMap _ hb1
  have h3 := inverse_hotspot _ _ hb2 _ r M B h2
  have hb3 := rotation.symm.toHomeomorph.isOpenMap _ hb2
  have h4 := Packet07DrivenAxialHotspot.rotate_hotspot θ _ _ hb3 _ r M B h3
  simp only [Set.image_image] at h4
  exact h4

end OQ14.Packet07DrivenFrameHotspot
#print axioms OQ14.Packet07DrivenFrameHotspot.cyclic_hotspot
#print axioms OQ14.Packet07DrivenFrameHotspot.rotate_twice
#print axioms OQ14.Packet07DrivenFrameHotspot.inverse_hotspot
#print axioms OQ14.Packet07DrivenFrameHotspot.frame_hotspot

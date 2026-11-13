import Packet06RigidInitial
import Packet07DrivenRigidBoundary

/-! Rigid frame preserves the exact two-interface three-value material law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06RigidMaterialShape
open Set Metric Maxwell Packet06RigidHotspotState Packet06RigidHotspotFrame Packet06RigidMaterialValues
  Packet06ModalHotspotExistence Packet07PlaneFrame Packet07DrivenRigidHotspot
abbrev Space := Maxwell.Space

theorem material_shape {N : ℕ} {z : ℂ} {r M B : ℝ} (θ φ : ℝ) (a : Space)
    (d : State N z r M B) (outer : Set Space) (n η K : ℝ)
    (houter : IsOpen outer) (hsubset : d.body ⊆ outer)
    (hinnerSmooth : SmoothBoundary d.body) (houterSmooth : SmoothBoundary outer)
    (hlaw : ∀ x, MaterialMaxwell.dielectric d.material x =
      (by classical exact if x ∈ d.body then (1+η)*n^2 else if x ∈ outer then n^2 else 1))
    (hbound : ∀ x, 1 ≤ MaterialMaxwell.dielectric d.material x ∧ MaterialMaxwell.dielectric d.material x ≤ K^2) :
    let out := Packet07DrivenRigidHotspot.placement θ φ a '' outer
    IsOpen out ∧ (transform θ φ a d).body ⊆ out ∧ SmoothBoundary (transform θ φ a d).body ∧ SmoothBoundary out ∧
    (∀ y, MaterialMaxwell.dielectric (transform θ φ a d).material y =
      (by classical exact if y ∈ (transform θ φ a d).body then (1+η)*n^2 else if y ∈ out then n^2 else 1)) ∧
    ∀ y, 1 ≤ MaterialMaxwell.dielectric (transform θ φ a d).material y ∧
      MaterialMaxwell.dielectric (transform θ φ a d).material y ≤ K^2 := by
  classical
  let h := Packet07DrivenRigidHotspot.placement θ φ a
  have hb : (transform θ φ a d).body = h '' d.body := by
    rw [frame_body]
    rfl
  have ho : IsOpen (h '' outer) := h.isOpenMap _ houter
  have hs : h '' d.body ⊆ h '' outer := Set.image_subset _ hsubset
  have hbi : SmoothBoundary (h '' d.body) := Packet07DrivenRigidBoundary.smooth_boundary θ φ a _ hinnerSmooth
  have hbo : SmoothBoundary (h '' outer) := Packet07DrivenRigidBoundary.smooth_boundary θ φ a _ houterSmooth
  refine ⟨ho,by rw [hb]; exact hs,by rw [hb]; exact hbi,hbo,?_,?_⟩
  · intro y
    let x := h.symm y
    have hy : h x=y := h.apply_symm_apply y
    have hv := frame_value θ φ a d x
    change MaterialMaxwell.dielectric (transform θ φ a d).material (h x) = _ at hv
    rw [← hy,hv,hlaw,hb]
    have hmem1 : h x ∈ h '' d.body ↔ x ∈ d.body := h.injective.mem_set_image
    have hmem2 : h x ∈ h '' outer ↔ x ∈ outer := h.injective.mem_set_image
    rw [hmem1,hmem2]
  · intro y
    let x := h.symm y
    have hy : h x=y := h.apply_symm_apply y
    have hv := frame_value θ φ a d x
    change MaterialMaxwell.dielectric (transform θ φ a d).material (h x) = _ at hv
    rw [← hy,hv]
    exact hbound x
end OQ14.Packet06RigidMaterialShape
#print axioms OQ14.Packet06RigidMaterialShape.material_shape

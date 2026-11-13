import Packet06RigidMaterialShape
import Packet06RigidFrameGeometry
import Packet07PlanePatch

/-! Actual normalized modal hotspots in a prescribed affine plane and open patch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06AffineModalExistence
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedExistence Packet06RigidInitial
  Packet06RigidHotspotState Packet06RigidHotspotFrame Packet06RigidCollar Packet06RigidCollarFrame
  Packet07PlaneFrame Packet07PlaneCoordinates Packet07PlanePatch Packet06RigidFrameGeometry
abbrev Space := Maxwell.Space

theorem exists_affine_modal_hotspots (N : ℕ) (K target Q ρ M : ℝ)
    (hK : 1 < K) (htarget : 0 < target) (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (n a : Space) (hn : ‖n‖=1) (O : Set Space) (hO : IsOpen O)
    (hne : (affinePlane n a ∩ O).Nonempty) :
    ∃ (θ φ : ℝ) (d : Device N) (hv : Valid d K target Q ρ M (embed θ φ a ⁻¹' O)) (hr : Retained d),
      normalRotation θ φ (EuclideanSpace.single 2 1)=n ∧
      let base := initial d K target Q ρ M (embed θ φ a ⁻¹' O) hv hr
      let final := transform θ φ a base
      let collars := transformCollars θ φ a d.collar
      let outer := Packet07DrivenRigidHotspot.placement θ φ a '' d.outerBody
      final.plane = affinePlane n a ∧
      d.frequency.re=target ∧ d.frequency.im<0 ∧ Q < d.frequency.re/(-2*d.frequency.im) ∧
      0 < d.radius ∧ d.radius ≤ ρ ∧ 0 ≤ d.collarBound ∧
      Packet06OutgoingMode.IsActualOutgoingMode final.material d.frequency final.supportRadius final.unknown ∧
      IsOpen outer ∧ final.body ⊆ outer ∧ SmoothBoundary final.body ∧ SmoothBoundary outer ∧
      (∀ y, MaterialMaxwell.dielectric final.material y =
        (by classical exact if y ∈ final.body then (1+d.η)*d.n^2 else if y ∈ outer then d.n^2 else 1)) ∧
      (∀ y, 1 ≤ MaterialMaxwell.dielectric final.material y ∧ MaterialMaxwell.dielectric final.material y ≤ K^2) ∧
      (∀ i, final.center i ∈ affinePlane n a ∩ O) ∧ Function.Injective final.center ∧
      (∀ i y, y ∈ ball (final.center i) d.radius → projection θ φ a y ∈ O) ∧
      (∀ i j, i ≠ j → Disjoint (ball (final.center i) d.radius) (ball (final.center j) d.radius)) ∧
      HasCollars final collars ∧ ∀ i, Packet06AxialHotspot.AxialHotspot final.material d.frequency final.unknown
        final.body final.plane (final.center i) d.radius M d.collarBound := by
  obtain ⟨θ,φ,hframe⟩ := exists_frame n hn
  have hne' : (affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O).Nonempty := by
    rw [hframe]; exact hne
  obtain ⟨hP,hPne,hPimage⟩ := patch_pullback θ φ a O hO hne'
  obtain ⟨d,hv,hr⟩ := exists_retained_modal_hotspots N K target Q ρ M hK htarget hQ hρ _ hP hPne
  let base := initial d K target Q ρ M (embed θ φ a ⁻¹' O) hv hr
  let final := transform θ φ a base
  have hgeom := transformed_geometry θ φ a base O hv.centers_planar hv.projected_balls hv.centers_injective hv.disjoint_balls
  have hshape := Packet06RigidMaterialShape.material_shape θ φ a base d.outerBody d.n d.η K
    hv.outer_open hv.inner_subset hv.inner_smooth hv.outer_smooth hv.material_values hv.material_bounds
  have hplane : final.plane = affinePlane n a := by
    rw [frame_plane]
    change (fun x => a + normalRotation θ φ x) '' {x : Space | x 2=0} = _
    rw [plane_image,hframe]
  have hcollar := transform_collars θ φ a base d.collar (initial_collars d K target Q ρ M _ hv hr)
  refine ⟨θ,φ,d,hv,hr,hframe,?_,hv.frequency_real,hv.frequency_imag,hv.quality,hv.radius_pos,hv.radius_bound,
    hv.bound_nonneg,Packet06RigidStateOutgoing.actual_outgoing final,?_,?_,?_,?_,?_,?_,?_,hgeom.2.1,?_,hgeom.2.2.2,hcollar,final.hotspots⟩
  · exact hplane
  · exact hshape.1
  · exact hshape.2.1
  · exact hshape.2.2.1
  · exact hshape.2.2.2.1
  · exact hshape.2.2.2.2.1
  · exact hshape.2.2.2.2.2
  · simpa only [hframe] using hgeom.1
  · exact hgeom.2.2.1
end OQ14.Packet06AffineModalExistence
#print axioms OQ14.Packet06AffineModalExistence.exists_affine_modal_hotspots

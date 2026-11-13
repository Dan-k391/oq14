import Packet06AffineModalPole

/-! Literal fixed-permittivity, fixed-diameter affine-plane modal theorem,
including the same actual mode's transported-sector observed pole. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.Packet06FinalAffineModal
open Set Metric Maxwell Packet06ModalHotspotExistence Packet06ModalRetainedExistence Packet06RigidInitial
  Packet06RigidHotspotState Packet06RigidHotspotFrame Packet06RigidCollar Packet06RigidCollarFrame
  Packet07PlaneFrame Packet07PlaneCoordinates

theorem exists_physical_modal_hotspots (N : ℕ) (ε target Q ℓ M : ℝ)
    (hε : 1 < ε) (htarget : 0 < target) (hQ : 0 ≤ Q) (hℓ : 0 < ℓ)
    (n a : Maxwell.Space) (hn : ‖n‖=1) (O : Set Maxwell.Space) (hO : IsOpen O)
    (hne : (affinePlane n a ∩ O).Nonempty) :
    ∃ (θ φ : ℝ) (d : Device N)
      (hv : Valid d (Real.sqrt ε) target Q (ℓ/4) M (embed θ φ a ⁻¹' O)) (hr : Retained d),
      normalRotation θ φ (EuclideanSpace.single 2 1)=n ∧
      let base := initial d (Real.sqrt ε) target Q (ℓ/4) M (embed θ φ a ⁻¹' O) hv hr
      let final := transform θ φ a base
      let collars := transformCollars θ φ a d.collar
      let outer := Packet07DrivenRigidHotspot.placement θ φ a '' d.outerBody
      let ps := Packet06FullFrameObservedPole.full θ φ a (Packet06RigidPencilState.initial d.material d.supportRadius
        (Packet06ModalRetainedHost.supportRadius_nonneg d) hv.material_support)
      final.plane = affinePlane n a ∧
      d.frequency.re=target ∧ d.frequency.im<0 ∧ Q < d.frequency.re/(-2*d.frequency.im) ∧
      0 < d.radius ∧ 2*d.radius < ℓ ∧ 0 ≤ d.collarBound ∧
      Packet06OutgoingMode.IsActualOutgoingMode final.material d.frequency final.supportRadius final.unknown ∧
      Packet06GenericObservedPole.SimpleObservedPole final.material final.supportRadius
        (Packet06RigidStateSector.embedding ps d.dilation d.dilation_pos d.translation)
        (Packet06RigidStateSector.pencil ps d.dilation d.dilation_pos d.translation) d.frequency d.baseUnknown ∧
      Packet06RigidStateSync.Matches base.unknown ps final ∧
      IsOpen outer ∧ final.body ⊆ outer ∧ SmoothBoundary final.body ∧ SmoothBoundary outer ∧
      (∀ y, MaterialMaxwell.dielectric final.material y =
        (by classical exact if y ∈ final.body then (1+d.η)*d.n^2 else if y ∈ outer then d.n^2 else 1)) ∧
      (∀ y, 1 ≤ MaterialMaxwell.dielectric final.material y ∧ MaterialMaxwell.dielectric final.material y ≤ ε) ∧
      (∀ i, final.center i ∈ affinePlane n a ∩ O) ∧ Function.Injective final.center ∧
      (∀ i y, y ∈ ball (final.center i) d.radius → projection θ φ a y ∈ O) ∧
      (∀ i j, i ≠ j → Disjoint (ball (final.center i) d.radius) (ball (final.center j) d.radius)) ∧
      HasCollars final collars ∧ ∀ i, Packet06AxialHotspot.AxialHotspot final.material d.frequency final.unknown
        final.body final.plane (final.center i) d.radius M d.collarBound := by
  have hK : 1 < Real.sqrt ε := by
    have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num) hε
    simpa using h
  obtain ⟨θ,φ,d,hv,hr,hframe,hplane,hre,him,hquality,hrad,hradbound,hB,hout,
    hopen,hsub,hinner,houter,hlaw,hbound,hcenters,hinj,hproject,hdisjoint,hcollars,hhot⟩ :=
      Packet06AffineModalExistence.exists_affine_modal_hotspots N (Real.sqrt ε) target Q (ℓ/4) M
        hK htarget hQ (by positivity) n a hn O hO hne
  have hpole := Packet06AffineModalPole.final_observed_pole d (Real.sqrt ε) target Q (ℓ/4) M _ hv hr θ φ a
  have hsync := Packet06RigidStateSync.full_sync θ φ a (initial d (Real.sqrt ε) target Q (ℓ/4) M _ hv hr)
  refine ⟨θ,φ,d,hv,hr,hframe,hplane,hre,him,hquality,hrad,by linarith,hB,hout,hpole,
    hsync,hopen,hsub,hinner,houter,hlaw,?_,hcenters,hinj,hproject,hdisjoint,hcollars,hhot⟩
  intro y
  have h := hbound y
  rw [Real.sq_sqrt (le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hε))] at h
  exact h
end OQ14.Packet06FinalAffineModal
#print axioms OQ14.Packet06FinalAffineModal.exists_physical_modal_hotspots

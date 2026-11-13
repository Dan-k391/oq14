import Packet07DrivenUniformFixedTargetStrong
import Packet07DrivenRigidGeometry
import Packet07DrivenRigidFields
import Packet07DrivenActualGood

/-! Arbitrary-plane exact-frequency driven fields with simultaneous attained hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 10000
namespace OQ14.Packet07DrivenPlaneHotspots
open Filter Set Metric Maxwell Packet07PlanarCenters Packet07PlaneCoordinates Packet07PlaneFrame
  Packet07DrivenRigidHotspot Packet07DrivenUniformHotspot Packet07DrivenFrameMaxwell
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem plane_hotspots (N : ℕ) (hN : 0 < N) (n a : Space) (hn : ‖n‖=1)
    (O : Set Space) (hO : IsOpen O) (hne : (affinePlane n a ∩ O).Nonempty)
    (d t target ell : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) (htarget : 0 < target) (hell : 0 < ell) :
    ∃ (θ φ : ℝ) (P : Set Plane) (g : Packet07PlanarSetup.Setup N (ball (0 : Plane) 1) d t)
      (u : Plane) (freq s : ℝ) (input : Input) (B : Fin N → ℝ),
      normalRotation θ φ (EuclideanSpace.single 2 1)=n ∧
      embed θ φ a '' P = affinePlane n a ∩ O ∧ 0 < freq ∧ 0 < s ∧ s*freq=target ∧ input ≠ 0 ∧
      (∀ i, embed θ φ a (u+s⁻¹ • g.points i) ∈ affinePlane n a ∩ O) ∧
      2*((g.radius/2)/s) < ell ∧ (∀ i, 0 ≤ B i) ∧
      (∀ j, Packet06ComplexAffine.TestMaxwellC (target : ℂ)
        (fun x => MaterialMaxwell.dielectric (g.rounded j)
          (Packet07AffineGeometry.map s (planeEmbed u) ((normalRotation θ φ).symm (x-a))))
        (field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input)))
        (field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic freq j input)))) ∧
      ∀ M : Fin N → ℝ, ∀ᶠ j : ℕ in atTop, ∀ i,
        HotspotAbove (field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input)))
          (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹'
            CommonBinaryInterface.body g.dataFamily g.radii g.centers j))
          (embed θ φ a (u+s⁻¹ • g.points i)) ((g.radius/2)/s) (M i) (s*B i) := by
  obtain ⟨θ,φ,P,hframe,hP,hneP,himage,_,_,_,_,_⟩ :=
    Packet07PlaneArbitrary.arbitrary_plane_patch n a hn O hO hne
  obtain ⟨g,u,freq,s,input,hu,hfreq,hcommon,hs,hsk,hinput,hpoints,hsize,hdiam,hdisj,hpatch,hballs,
    hpower,hunit,htan,hsmooth,hsphere,he,hh,hevent,B,hB,hhot⟩ :=
    Packet07DrivenUniformFixedTargetStrong.fixed_target_hotspots N hN P hP hneP d t target ell hd ht ht1 htarget hell
  refine ⟨θ,φ,P,g,u,freq,s,input,B,hframe,himage,hfreq,hs,hsk,hinput,?_,hdiam,hB,?_,?_⟩
  · intro i
    rw [←himage]
    exact ⟨_,hpoints i,rfl⟩
  · intro j
    have hgood := Packet07DrivenActualGood.actual_good g freq input hcommon j
    have hgood' := Packet07DrivenAffineGood.affine_good s hs (planeEmbed u) freq _ _ _ hgood
    have hM := Packet07DrivenRigidFields.rigid_maxwell θ φ (s*freq) a _ _ _ hgood'
    simpa only [hsk] using hM
  · intro M
    filter_upwards [hhot M,hevent] with j hj hj'
    intro i
    have hi := rigid_hotspot θ φ a _ _ hj'.2.1 _ _ _ _ (hj i)
    simpa only [placement_embed] using hi
end OQ14.Packet07DrivenPlaneHotspots
#print axioms OQ14.Packet07DrivenPlaneHotspots.plane_hotspots

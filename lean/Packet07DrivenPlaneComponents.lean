import Packet07DrivenUniformFixedTargetStrong
import Packet07DrivenRigidGeometry
import Packet07DrivenRigidFields
import Packet07DrivenActualGood
import Packet07DrivenRigidAngular
import Packet07DrivenRigidBoundary
import Packet07DrivenRigidAE

/-! Arbitrary-plane exact-frequency driven fields with simultaneous attained hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 10000
namespace OQ14.Packet07DrivenPlaneComponents
open Filter MeasureTheory Set Metric Maxwell Packet07PlanarCenters Packet07PlaneCoordinates Packet07PlaneFrame
  Packet07DrivenRigidHotspot Packet07DrivenUniformHotspot Packet07DrivenFrameMaxwell
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem plane_components (N : ℕ) (hN : 0 < N) (n a : Space) (hn : ‖n‖=1)
    (O : Set Space) (hO : IsOpen O) (hne : (affinePlane n a ∩ O).Nonempty)
    (d t target ell : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) (htarget : 0 < target) (hell : 0 < ell) :
    ∃ (θ φ : ℝ) (P : Set Plane) (g : Packet07PlanarSetup.Setup N (ball (0 : Plane) 1) d t)
      (u : Plane) (freq s : ℝ) (input : Input) (B : Fin N → ℝ),
      normalRotation θ φ (EuclideanSpace.single 2 1)=n ∧
      embed θ φ a '' P = affinePlane n a ∩ O ∧ 0 < freq ∧ 0 < s ∧ s*freq=target ∧ input ≠ 0 ∧
      (∀ i, embed θ φ a (u+s⁻¹ • g.points i) ∈ affinePlane n a ∩ O) ∧
      2*((g.radius/2)/s) < ell ∧
      (∀ i j, i ≠ j → Disjoint (closedBall (embed θ φ a (u+s⁻¹ • g.points i)) ((g.radius/2)/s))
        (closedBall (embed θ φ a (u+s⁻¹ • g.points j)) ((g.radius/2)/s))) ∧
      (∀ i, 0 ≤ B i) ∧
      (let A := Packet07DrivenRigidAngular.amplitude θ φ target a
        (Packet07AngularTranslation.translatedAmplitude target (planeEmbed u)
          (FiniteVectorAngular.amplitude ((s : ℂ) • input)))
       ((2 * Real.pi^2 / target^2) * ‖ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ A‖^2 = 1) ∧
       (∀ n, @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (A n)=0) ∧
       (∃ F : Fin 3 → Space → ℂ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) ∧
         ∀ (n : SphereHarmonicBasis.Sphere) i, F i n=A n i) ∧
       AngularHerglotz.electric target (fun n j => A n j) =
         field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).E) ∧
       AngularHerglotz.magnetic target (fun n j => A n j) =
         field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H)) ∧
      (∀ i x, dist x (embed θ φ a (u+s⁻¹ • g.points i)) ≤ (g.radius/2)/s →
        projection θ φ a x ∈ affinePlane n a ∩ O) ∧
      (∀ᶠ j : ℕ in atTop,
        IsOpen (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j)) ∧
        (∀ x ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j),
          projection θ φ a x ∈ affinePlane n a ∩ O) ∧
        (∀ i : Fin N, ∀ up : Bool,
          (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i up)).Nonempty) ∧
        (∀ i l : Fin N × Bool, i ≠ l → Disjoint
          (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2))
          (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j l.1 l.2))) ∧
        (∀ i : Fin N × Bool, ∀ x ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2),
          connectedComponentIn (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j)) x =
            placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2)) ∧
        (∀ x ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j),
          ∃! i : Fin N × Bool, connectedComponentIn
            (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j)) x =
            placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' Packet07LobeGeometry.lobe g.dataFamily g.radii g.centers j i.1 i.2)) ∧
        (∀ x : Space, (Packet07AffineMaxwell.affineCoeff s (planeEmbed u) (g.rounded j)).value
          (VectorFourier.coordinateMap ((normalRotation θ φ).symm (x-a))) =
            (by classical exact if x ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) then d else 0)) ∧
        (∀ x ∈ frontier (placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j)),
          ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
            ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
              (y ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) ↔ 0 < F y))) ∧
      (∀ᶠ j : ℕ in atTop,
        let ρ := DynamicVolume.source (g.rounded j) (Packet07SelectedRadiation.actualUnknown g freq j input)
        (∀ᵐ x : Space ∂volume, g.enclosing < ‖s • ((normalRotation θ φ).symm (x-a)-planeEmbed u)‖ →
          field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.electric freq j input)) x =
          field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).E) x +
          field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric freq ρ)) x) ∧
        (∀ x, field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic freq j input)) x =
          field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H) x +
          field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic freq ρ)) x) ∧
        Packet07DrivenRotatedOutgoing.OutAt target (placement θ φ a (planeEmbed u))
          (field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (ExteriorContinuity.electric freq ρ)))
          (frameField θ φ (MaxwellFarField.electricAmplitude freq ρ)) ∧
        Packet07DrivenRotatedOutgoing.OutAt target (placement θ φ a (planeEmbed u))
          (field θ φ a (Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic freq ρ)))
          (frameField θ φ (MaxwellFarField.magneticAmplitude freq ρ))) ∧
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
  refine ⟨θ,φ,P,g,u,freq,s,input,B,hframe,himage,hfreq,hs,hsk,hinput,?_,hdiam,?_,hB,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [←himage]
    exact ⟨_,hpoints i,rfl⟩
  · intro i j hij
    rw [←placement_embed,←placement_embed,←Packet07DrivenRigidGeometry.placement_ball,
      ←Packet07DrivenRigidGeometry.placement_ball]
    exact (hdisj i j hij).image (placement θ φ a).injective.injOn (subset_univ _) (subset_univ _)
  · dsimp only
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [Packet07DrivenRigidAngular.amplitude_norm]
      exact hunit
    · exact Packet07DrivenRigidAngular.amplitude_tangent θ φ target a _ htan
    · let F := Packet07DrivenAngularTranslationSmooth.extension target a
          (Packet07DrivenFrameAngularSmooth.extension θ φ (Packet07SmoothAngular.extension target (planeEmbed u) ((s : ℂ) • input)))
      refine ⟨F,?_,?_⟩
      · exact Packet07DrivenAngularTranslationSmooth.extension_smooth target a _
          (Packet07DrivenFrameAngularSmooth.extension_smooth θ φ _ hsmooth)
      · exact Packet07DrivenAngularTranslationSmooth.extension_on_sphere target a _ _
          (Packet07DrivenFrameAngularSmooth.extension_on_sphere θ φ _ _ hsphere)
    · rw [Packet07DrivenRigidAngular.electric]
      have hf : AngularHerglotz.electric target (fun n j => Packet07AngularTranslation.translatedAmplitude target (planeEmbed u) (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n j) = Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).E := by
        funext x i
        exact he x i
      rw [hf]
    · rw [Packet07DrivenRigidAngular.magnetic]
      have hf : AngularHerglotz.magnetic target (fun n j => Packet07AngularTranslation.translatedAmplitude target (planeEmbed u) (FiniteVectorAngular.amplitude ((s : ℂ) • input)) n j) = Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H := by
        funext x i
        exact hh x i
      rw [hf]
  · intro i x hx
    rw [←himage]
    let y := (placement θ φ a).symm x
    have hx' : x=placement θ φ a y := ((placement θ φ a).apply_symm_apply x).symm
    rw [hx',←placement_embed,Packet07DrivenRigidGeometry.placement_dist] at hx
    rw [hx',Packet07DrivenRigidGeometry.placement_projection]
    exact ⟨_,hballs i y hx,rfl⟩
  · filter_upwards [hevent] with j hj
    refine ⟨(placement θ φ a).isOpenMap _ hj.2.1,?_,?_,?_,?_,?_,?_,?_⟩
    · rintro x ⟨y,hy,rfl⟩
      rw [Packet07DrivenRigidGeometry.placement_projection,←himage]
      exact ⟨_,hj.2.2.1 y hy,rfl⟩
    · intro i up
      exact (hj.2.2.2.1 i up).image _
    · intro i l hne
      exact (hj.2.2.2.2.1 i l hne).image (placement θ φ a).injective.injOn (subset_univ _) (subset_univ _)
    · intro i x hx
      obtain ⟨y,hy,rfl⟩ := hx
      have hc := hj.2.2.2.2.2.1 i y hy
      have hybody : y ∈ (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) := by
        apply connectedComponentIn_subset
        rw [hc]
        exact hy
      rw [←(placement θ φ a).image_connectedComponentIn hybody,hc]
    · rintro x ⟨y,hy,rfl⟩
      obtain ⟨i,hi,huniq⟩ := hj.2.2.2.2.2.2.1 y hy
      refine ⟨i,?_,?_⟩
      · rw [←(placement θ φ a).image_connectedComponentIn hy,hi]
      · intro k hk
        apply huniq k
        rw [←(placement θ φ a).image_connectedComponentIn hy] at hk
        exact (placement θ φ a).injective.image_injective hk
    · intro x
      have he : ((normalRotation θ φ).symm (x-a)) ∈ (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) ↔
          x ∈ placement θ φ a '' (Packet07AffineGeometry.map s (planeEmbed u) ⁻¹' CommonBinaryInterface.body g.dataFamily g.radii g.centers j) := by
        rw [(placement θ φ a).image_eq_preimage]
        rfl
      rw [←he]
      exact hj.2.2.2.2.2.2.2.2.1 _
    · exact Packet07DrivenRigidBoundary.smooth_boundary θ φ a _ hj.2.2.2.2.2.2.2.1
  · filter_upwards [hevent] with j hj
    obtain ⟨hE,hH,houtE,houtH⟩ := hj.2.2.2.2.2.2.2.2.2
    refine ⟨?_,?_,?_,?_⟩
    · apply Packet07DrivenRigidAE.exterior_decomposition θ φ a (fun x => g.enclosing < ‖s • (x-planeEmbed u)‖)
      filter_upwards [hE] with x hx hp
      funext i
      exact hx hp i
    · have heq : Packet07AffineMaxwell.affineField s (planeEmbed u) (g.magnetic freq j input) =
          fun x => Packet07AffineMaxwell.affineField s (planeEmbed u) (FiniteAngularHerglotz.incident freq input).H x +
            Packet07AffineMaxwell.affineField s (planeEmbed u) (MagneticResponse.magnetic freq (DynamicVolume.source (g.rounded j) (Packet07SelectedRadiation.actualUnknown g freq j input))) x := by
        funext x i
        exact hH x i
      intro x
      rw [heq,Packet07DrivenRigidAE.field_add]
    · exact Packet07DrivenRigidFields.rigid_outgoing θ φ target a _ _ _ houtE
    · exact Packet07DrivenRigidFields.rigid_outgoing θ φ target a _ _ _ houtH
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
end OQ14.Packet07DrivenPlaneComponents
#print axioms OQ14.Packet07DrivenPlaneComponents.plane_components

import Packet07DrivenPlaneComplete
import Packet07DrivenUniformMaterialCeiling

/-! Arbitrarily prescribed positive material ceiling for the same complete driven configuration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
namespace OQ14.Packet07DrivenPlaneCeiling
open Filter MeasureTheory Set Metric Maxwell Packet07PlanarCenters Packet07PlaneCoordinates Packet07PlaneFrame
  Packet07DrivenRigidHotspot Packet07DrivenUniformHotspot Packet07DrivenFrameMaxwell
open scoped Topology
abbrev Plane := Packet07PlanarCenters.Plane
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem plane_ceiling (N : ℕ) (hN : 0 < N) (n a : Space) (hn : ‖n‖=1)
    (O : Set Space) (hO : IsOpen O) (hne : (affinePlane n a ∩ O).Nonempty)
    (ceiling target ell : ℝ) (hceiling : 1 < ceiling) (htarget : 0 < target) (hell : 0 < ell) :
    ∃ d t : ℝ, 0 < d ∧ 1+d ≤ ceiling ∧ 0 < t ∧ t < 1 ∧ ∃ (θ φ : ℝ) (P : Set Plane) (g : Packet07PlanarSetup.Setup N (ball (0 : Plane) 1) d t)
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
  obtain ⟨d,hd,hbound⟩ := Packet07DrivenUniformMaterialCeiling.positive_contrast_below ceiling hceiling
  refine ⟨d,3/4,hd,hbound,by norm_num,by norm_num,?_⟩
  exact Packet07DrivenPlaneComplete.plane_complete N hN n a hn O hO hne d (3/4) target ell hd (by norm_num) (by norm_num) htarget hell
end OQ14.Packet07DrivenPlaneCeiling
#print axioms OQ14.Packet07DrivenPlaneCeiling.plane_ceiling

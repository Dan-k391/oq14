import Packet06StrongLocalizedFrameVolume
import Packet06StrongLocalizedVolumeFamily
import Packet06LocalizedVolumeState
import Packet06RigidFrameGeometry
import Packet07PlaneArbitrary
import Packet06RigidGenericPole
import Packet06LocalizedVolumeCollars
import Packet06RigidCollarFrame
import Packet06RigidClosedGeometry
import Packet06LocalizedVolumeMaterialBound
import Packet06RigidPhasePermittivity
import Packet06NeighborhoodTraceIntrinsic

/-! The one actual localized rounded modal family, carried to a prescribed
plane, retains its genuine phase-weighted maxima and volume limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06StrongAffineVolumeFamily
open Filter Metric Set Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06PlacedKernel Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedRoundedVolumeLimits
  Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum Packet06PhysicalVolumeLimits
  Packet06NeighborhoodWeighted Packet06NeighborhoodWeightedFrame
  Packet06RigidWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet07PlaneFrame Packet07PlaneCoordinates Packet07PlanePatch
open scoped Topology
abbrev Space := Maxwell.Space

theorem exists_strong_affine_volume_family (N : ℕ) (K target Q ell : ℝ)
    (hK : 1 < K) (ht : 0 < target) (hQ : 0 ≤ Q) (hell : 0 < ell)
    (normal origin : Space) (hnormal : ‖normal‖=1) (O : Set Space) (hO : IsOpen O)
    (hne : (affinePlane normal origin ∩ O).Nonempty) :
    ∃ (θ φ n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η) (g : Geometry N n)
      (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (r B : ℝ)
      (u : EuclideanSpace ℝ (Fin 2)) (A : Fin N → Set Space) (md : ℕ → Fin N → MaximumData)
      (side : ℕ → Fin N → Bool) (point : ℕ → Fin N → Space)
      (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (J : ℕ)
      (q : ∀ j, Packet06RigidHotspotState.State N (((s (j+J)) : ℂ)*z (j+J))
        (r/s (j+J)) 0 (scale (s (j+J))*B)),
      normalRotation θ φ (EuclideanSpace.single 2 1)=normal ∧ n < K ∧ 0 < η ∧ 0 < r ∧ r < g.radius ∧
      (∀ j, (q j).material = placedCoefficient (s (j+J)) (Packet07PlanarCenters.planeEmbed u) (rounded n hn g η hη (j+J)) ∧
        (q j).unknown = placedUnknown (s (j+J)) (Packet07PlanarCenters.planeEmbed u) (v (j+J)) ∧
        (q j).body = placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) '' body g (j+J) ∧
        ∀ i, (q j).center i = placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∧
      (∀ j, Packet06SimpleCertificate.Certified (rounded n hn g η hη (j+J)) 1 (z (j+J)) (v (j+J))) ∧
      (∀ j,
        let p := Packet06FullFrameObservedPole.full θ φ origin
          (Packet06RigidPencilState.initial (q j).material (q j).supportRadius (q j).support_nonnegative (q j).support)
        let final := Packet06RigidHotspotFrame.transform θ φ origin (q j)
        Packet06RigidStateSector.embedding p (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (v (j+J)) = final.unknown ∧
        Packet06GenericObservedPole.SimpleObservedPole final.material final.supportRadius
          (Packet06RigidStateSector.embedding p (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u))
          (Packet06RigidStateSector.pencil p (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u))
          (((s (j+J)) : ℂ)*z (j+J)) (v (j+J))) ∧
      (∀ j, Packet06RigidCollar.HasCollars (Packet06RigidHotspotFrame.transform θ φ origin (q j))
        (Packet06RigidCollarFrame.transformCollars θ φ origin
          (fun i => placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) '' A i))) ∧
      (∀ j,
        let final := Packet06RigidHotspotFrame.transform θ φ origin (q j)
        let outer := Packet07DrivenRigidHotspot.placement θ φ origin ''
          (placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) '' ball (0 : Space) 1)
        IsOpen outer ∧ final.body ⊆ outer ∧ Packet06ModalHotspotExistence.SmoothBoundary final.body ∧
        Packet06ModalHotspotExistence.SmoothBoundary outer ∧
        ∀ y, MaterialMaxwell.dielectric final.material y =
          (by classical exact if y ∈ final.body then (1+η)*n^2 else if y ∈ outer then n^2 else 1)) ∧
      (∀ j i y, y ∈ closedBall ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).center i) (r/s (j+J)) →
        (y ∈ (Packet06RigidHotspotFrame.transform θ φ origin (q j)).body →
          MaterialMaxwell.dielectric (Packet06RigidHotspotFrame.transform θ φ origin (q j)).material y = phasePermittivity n η true) ∧
        (y ∉ closure ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).body) →
          MaterialMaxwell.dielectric (Packet06RigidHotspotFrame.transform θ φ origin (q j)).material y = phasePermittivity n η false)) ∧
      (∀ j, r/s (j+J) < g.radius/s (j+J)) ∧
      (∀ j i, Packet06NeighborhoodWeightedFrame.sets θ φ origin
        (closedBall (placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (g.radius/s (j+J))) =
        closedBall ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).center i) (g.radius/s (j+J))) ∧
      (∀ j y, 1 ≤ MaterialMaxwell.dielectric (Packet06RigidHotspotFrame.transform θ φ origin (q j)).material y ∧
        MaterialMaxwell.dielectric (Packet06RigidHotspotFrame.transform θ φ origin (q j)).material y ≤ K^2) ∧
      (∀ j, Packet06OutgoingMode.IsActualOutgoingMode (Packet06RigidHotspotFrame.transform θ φ origin (q j)).material
        (((s (j+J)) : ℂ)*z (j+J)) (Packet06RigidHotspotFrame.transform θ φ origin (q j)).supportRadius
        (Packet06RigidHotspotFrame.transform θ φ origin (q j)).unknown) ∧
      (∀ j, (((s (j+J)) : ℂ)*z (j+J)).re=target ∧ (((s (j+J)) : ℂ)*z (j+J)).im<0 ∧
        Q < (((s (j+J)) : ℂ)*z (j+J)).re/(-2*(((s (j+J)) : ℂ)*z (j+J)).im) ∧
        2*(r/s (j+J)) < ell) ∧
      (∀ j, (∀ i, (Packet06RigidHotspotFrame.transform θ φ origin (q j)).center i ∈ affinePlane normal origin ∩ O) ∧
        Function.Injective (Packet06RigidHotspotFrame.transform θ φ origin (q j)).center ∧
        (∀ i y, y ∈ closedBall ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).center i) (r/s (j+J)) →
          projection θ φ origin y ∈ O) ∧
        ∀ i k, i ≠ k → Disjoint (closedBall ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).center i) (r/s (j+J)))
          (closedBall ((Packet06RigidHotspotFrame.transform θ φ origin (q j)).center k) (r/s (j+J)))) ∧
      ∀ i,
    let K := fun j => closedBall (placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (g.radius/s (j+J))
    let inside := fun j => branches θ φ origin (transport (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (md (j+J) i).inside)
    let outside := fun j => branches θ φ origin (transport (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (md (j+J) i).outside)
    let W := fun j => scale (s (j+J))^2 * weighted n η (md (j+J) i) (side (j+J) i) (point (j+J) i)
    let sideF := fun j => side (j+J) i
    let pointF := fun j => Packet07DrivenRigidHotspot.placement θ φ origin (placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (point (j+J) i))

    (∀ j, Certificate (Packet06RigidHotspotFrame.transform θ φ origin (q j)) i (sets θ φ origin (K j)) n η
      (inside j) (outside j) (sideF j) (pointF j)) ∧
    (∀ j, W j = phasePermittivity n η (sideF j) *
      (physicalAmplitude (phaseField (inside j) (outside j) (sideF j)) (pointF j))^2) ∧
    Tendsto (fun j => (W j)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun j => amplitude (fun k => phaseField (inside j) (outside j) (sideF j) k (pointF j))) atTop atTop ∧
    ∃ (k : Fin 3) (ψ : ℕ → ℕ), StrictMono ψ ∧
      (∀ᶠ j in atTop, phaseField (inside (ψ j)) (outside (ψ j)) (sideF (ψ j)) k (pointF (ψ j)) ≠ 0) ∧
      Tendsto (fun j => (((phasePermittivity n η (sideF (ψ j)) : ℝ) : ℂ)*
        (phaseField (inside (ψ j)) (outside (ψ j)) (sideF (ψ j)) k (pointF (ψ j)))^2)⁻¹) atTop (𝓝 0) := by
  obtain ⟨θ,φ,hframe⟩ := exists_frame normal hnormal
  have hne' : (affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) origin ∩ O).Nonempty := by
    rw [hframe]; exact hne
  obtain ⟨hP,hPne,_⟩ := patch_pullback θ φ origin O hO hne'
  obtain ⟨n,η,hn,hη,g,z₀,z,v,r,u,md,side,point,s,hs,hr,hrg,hηpos,hu,hgeom,hnK,hz₀,hz,hst,hseq,
    ⟨A,B,hB,hA,hcollar,hhot⟩,hgood,hplaced,hmax,hactual,hdiv,hvol,hdir⟩ :=
    Packet06StrongLocalizedVolumeFamily.exists_strong_localized_volume_family N K target Q ell hK ht hQ hell _ hP hPne
  have htai : ∀ᶠ j in atTop,
      (0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      (∀ i, Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη j) (z j) (v j) (body g j) (g.center i) r 0 B) ∧
      (∀ i, Packet06StrongPlacedWeighted.StrongPlaced n hn g η hη j (z j) (v j) i r
        (md j i) (side j i) (point j i) (s j) (hs j) (Packet07PlanarCenters.planeEmbed u)) ∧
      (((s j : ℂ)*z j).re=target ∧ ((s j : ℂ)*z j).im<0 ∧ Q < ((s j : ℂ)*z j).re/(-2*((s j : ℂ)*z j).im)) ∧
      2*(r/s j) < ell ∧
      (∀ i, (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) 2=0 ∧
        Packet06PlanarProjection.project (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∈ (embed θ φ origin ⁻¹' O)) ∧
      Function.Injective (fun i => Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∧
      (∀ i y, y ∈ closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j) → Packet06PlanarProjection.project y ∈ (embed θ φ origin ⁻¹' O)) ∧
      ∀ i k, i ≠ k → Disjoint
        (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j))
        (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center k)) (r/s j)) := by
    filter_upwards [hgood,hhot 0,hactual,hplaced,hgeom] with j hg hh ha hp hge
    exact ⟨hg,hh,ha,⟨hp.1,hp.2.1,hp.2.2.1⟩,hge⟩
  obtain ⟨J,hJ⟩ := Filter.eventually_atTop.mp (((htai.and hcollar).and hplaced).and
    (Packet05RoundedModeMaterial.eventually_boundary_certificate g))
  have ht (j : ℕ) := (hJ (j+J) (by omega)).1.1.1
  have hcol (j : ℕ) := (hJ (j+J) (by omega)).1.1.2
  have hplace (j : ℕ) := (hJ (j+J) (by omega)).1.2
  have hsmooth (j : ℕ) := (hJ (j+J) (by omega)).2
  have hkernel (j : ℕ) : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη (j+J)) (z (j+J)) 1 (v (j+J))=0 := by
    obtain ⟨w,ψ,_,hk,_,_⟩ := (ht j).1.2.2.2.1
    exact hk
  have hN (j : ℕ) : Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη (j+J)) 1 (z (j+J)) (v (j+J))=1 := (ht j).1.2.2.2.2.1
  let q := fun j => Packet06LocalizedVolumeState.initial n hn g η hηpos (j+J) (z (j+J)) (v (j+J))
    (hkernel j) (hN j) r B hrg (ht j).2.1 (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u)
    (Packet07PlanarCenters.planeEmbed_coord u)
  refine ⟨θ,φ,n,η,hn,hη,g,z,v,r,B,u,A,md,side,point,s,hs,J,q,hframe,hnK,hηpos,hr,hrg,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact ⟨rfl,rfl,rfl,fun _ => rfl⟩
  · exact fun j => (ht j).1.2.2.2.1
  · intro j
    have hsym := Packet06RoundedPlacedPole.rounded_symmetries n hn g η hη (j+J)
    exact Packet06RigidGenericPole.same_actual_observed_pole (rounded n hn g η hη (j+J)) hsym.1 hsym.2
      1 (by norm_num) (Packet05RoundedModeSupport.rounded_support n hn g η hη (j+J))
      (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (z (j+J)) (v (j+J))
      ((ht j).1.2.2.2.1) (q j) rfl (by simp [q,Packet06LocalizedVolumeState.initial]) rfl θ φ origin
  · intro j
    have hinit := Packet06LocalizedVolumeCollars.initial_collars n hn g η hηpos (j+J) (z (j+J)) (v (j+J))
      (hkernel j) (hN j) r B hrg (ht j).2.1 (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u)
      (Packet07PlanarCenters.planeEmbed_coord u) A hA (hcol j)
    exact Packet06RigidCollarFrame.transform_collars θ φ origin (q j)
      (fun i => placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) '' A i) hinit
  · intro j
    have hshape := Packet06LocalizedVolumeMaterialBound.framed_material n hn g η hηpos (j+J)
      (z (j+J)) (v (j+J)) (hkernel j) (hN j) r B hrg (ht j).2.1
      (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (Packet07PlanarCenters.planeEmbed_coord u)
      (hsmooth j) K (hplace j).2.2.2.1 θ φ origin
    exact ⟨hshape.1,hshape.2.1,hshape.2.2.1,hshape.2.2.2.1,hshape.2.2.2.2.1⟩
  · intro j
    let outer := placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) '' ball (0 : Space) 1
    have hlaw : ∀ y, MaterialMaxwell.dielectric (q j).material y =
        (by classical exact if y ∈ (q j).body then (1+η)*n^2 else if y ∈ outer then n^2 else 1) := by
      intro y
      exact Packet06PlacedMaterialGeometry.placed_material_values n hn g η hη (j+J) (s (j+J)) (hs (j+J))
        (Packet07PlanarCenters.planeEmbed u) y
    have hhost : ∀ i, closedBall ((q j).center i) (r/s (j+J)) ⊆ outer := by
      intro i
      have hb : closedBall (g.center i) r ⊆ ball (0 : Space) 1 :=
        (closedBall_subset_closedBall (hrg.le.trans g.radius_outer)).trans (g.outer_inside i)
      change closedBall (placement (s (j+J)) (hs (j+J)) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s (j+J)) ⊆ _
      rw [← image_closedBall]
      exact Set.image_subset _ hb
    exact Packet06RigidPhasePermittivity.same_side_values θ φ origin (q j) outer n η hlaw hhost
  · intro j
    exact (div_lt_div_iff_of_pos_right (hs (j+J))).mpr hrg
  · intro j i
    rw [Packet06NeighborhoodWeightedFrame.sets_eq_image,Packet07DrivenRigidGeometry.placement_ball]
    rw [Packet06RigidHotspotFrame.frame_center]
    rfl
  · intro j y
    let w := (normalRotation θ φ).symm (y-origin)
    have hy : origin + normalRotation θ φ w = y := by simp [w]
    rw [←hy,Packet06RigidMaterialValues.frame_value]
    exact (hplace j).2.2.2.1 w
  · intro j
    exact Packet06RigidStateOutgoing.actual_outgoing _
  · intro j
    exact ⟨(ht j).2.2.2.1.1,(ht j).2.2.2.1.2.1,(ht j).2.2.2.1.2.2,(ht j).2.2.2.2.1⟩
  · intro j
    have hg := (ht j).2.2.2.2.2
    have hcg := Packet06RigidClosedGeometry.transformed_closed_geometry θ φ origin (q j) O
      hg.1 hg.2.2.1 hg.2.1 hg.2.2.2
    exact ⟨by simpa only [hframe] using hcg.1,hcg.2.1,hcg.2.2.1,hcg.2.2.2⟩
  · intro i
    exact Packet06StrongLocalizedFrameVolume.localized_strong_family_frame n hn g η hη z v r hrg md side point s hs
      (Packet07PlanarCenters.planeEmbed u) J (fun j => scale (s (j+J))*B) q
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun j => (ht j).2.2.1) (hmax.mono (fun j hj i => ⟨(hj i).1,(hj i).2.2⟩)) hdiv θ φ origin i
end OQ14.Packet06StrongAffineVolumeFamily
#print axioms OQ14.Packet06StrongAffineVolumeFamily.exists_strong_affine_volume_family

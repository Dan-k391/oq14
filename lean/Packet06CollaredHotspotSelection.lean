import Packet06PlacedActualCollar
import Packet06PlaceModeHotspots
import Packet06PlacedSmoothBoundary
import Packet06PlacedClusterBalls
import Packet06BoundedModalMaterial

/-! One late member of a fixed actual hotspot family simultaneously satisfies
the physical frequency, normalization, material, size and planar constraints. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06CollaredHotspotSelection
open MeasureTheory Metric Set Filter Maxwell Packet06ConcreteModalGeometry
  Packet06ConcreteModalRounding Packet06PlacedKernel Packet06PhysicalPlacement
  Packet06PlacementHomeomorph Packet06PlacedHotspot Packet06PlacedPhaseField
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem select_placed_collared_hotspots {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (K target Q ρ M : ℝ) (hK : 1 < K)
    (htarget : 0 < target) (hρ : 0 < ρ) (hceil : (1+η)*n^2 ≤ K^2)
    (P : Set Plane) (p : Plane) (rp : ℝ) (hrp : 0 < rp) (hpatch : ball p rp ⊆ P)
    (zbase z0 : ℂ) (hbase : 0 < zbase.re) (hnear : |z0.re-zbase.re| < zbase.re/2)
    (hcluster : ∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 (rp*target/(2*zbase.re)))
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (hz : Tendsto z atTop (𝓝 z0))
    (hgood : ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im<0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1)
    (r B : ℝ) (hr : 0 < r) (hrg : r ≤ g.radius) (hrρ : r ≤ ρ*(target/(2*zbase.re))) (hB : 0 ≤ B)
    (Extra : ℕ → Prop) (hExtra : ∀ᶠ j in atTop, Extra j)
    (A : Fin N → Set Space)
    (hA : ∀ i, IsOpen (A i) ∧ sphere (g.center i) r ⊆ A i ∧ A i ⊆ ball (0 : Space) 1)
    (hcollar : ∀ᶠ j in atTop, ∀ i : Fin N, ∀ᵐ x ∂volume.restrict (A i),
      Packet05ActualMaximum.physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x ≤ B)
    (hhot : ∀ T : ℝ, ∀ᶠ j in atTop, ∀ i,
      Packet06RoundedHotspot.HotspotAbove (rounded n hn g η hη j) (z j) (v j)
        (body g j) (g.center i) r T B) :
    ∃ j : ℕ, Extra j ∧
      let s := target/(z j).re
      let a := Packet07PlanarCenters.planeEmbed p
      let c := placedCoefficient s a (rounded n hn g η hη j)
      let zp := (s : ℂ)*z j
      let up := placedUnknown s a (v j)
      0 < s ∧ 0 < r/s ∧ r/s ≤ ρ ∧ zp.re=target ∧ zp.im<0 ∧ Q < zp.re/(-2*zp.im) ∧
      (∀ x : Space, 1 ≤ MaterialMaxwell.dielectric c x ∧ MaterialMaxwell.dielectric c x ≤ K^2) ∧
      (∀ x : Space, x ∉ closedBall 0 (1/s+‖a‖) → c.value (VectorFourier.coordinateMap x)=0) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
      ComplexConvolutionAnalytic.volumeBlock c zp (1/s+‖a‖) up=0 ∧
      Packet06PhysicalNormalization.reciprocalNorm c (1/s+‖a‖) zp up=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode c zp (1/s+‖a‖) up ∧
      (∀ i, (point s a (g.center i)) 2=0 ∧ Packet06PlanarProjection.project (point s a (g.center i)) ∈ P) ∧
      Function.Injective (fun i => point s a (g.center i)) ∧
      (∀ i y, y ∈ ball (point s a (g.center i)) (r/s) → Packet06PlanarProjection.project y ∈ P) ∧
      (∀ i k, i ≠ k → Disjoint (ball (point s a (g.center i)) (r/s)) (ball (point s a (g.center k)) (r/s))) ∧
      ∃ hs : 0 < s, 0 ≤ scale s*B ∧
        IsOpen (placement s hs a '' body g j) ∧
        (∀ x ∈ frontier (placement s hs a '' body g j), ∃ F : Space → ℝ,
          ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
          ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
            (y ∈ placement s hs a '' body g j ↔ 0 < F y)) ∧
        (∀ i, Packet06PlacedActualCollar.HasPhysicalCollar c zp up
          (point s a (g.center i)) (r/s) (scale s*B)) ∧
        ∀ i, PhysicalHotspot c zp up (placement s hs a '' body g j)
          (point s a (g.center i)) (r/s) M (scale s*B) := by
  let smin := target/(2*zbase.re)
  have hsmin : 0 < smin := div_pos htarget (by positivity)
  let T := max M 0/(Real.sqrt smin*smin)
  have hnearEv : ∀ᶠ j in atTop, |(z j).re-zbase.re| < zbase.re/2 :=
    (tendsto_order.mp (((Complex.continuous_re.continuousAt.tendsto.comp hz).sub_const zbase.re).abs)).2 _ hnear
  obtain ⟨j,hj,hclose,hhotj,hsmooth,hcollarj,hextra⟩ := (hgood.and (hnearEv.and ((hhot T).and
    ((Packet05RoundedModeMaterial.eventually_boundary_certificate g).and (hcollar.and hExtra))))).exists
  let s := target/(z j).re
  let a := Packet07PlanarCenters.planeEmbed p
  have hs : 0 < s := div_pos htarget hj.1
  have hb : IsOpen (body g j) := CommonBinaryInterface.body_open
    (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hball (i : Fin N) : closedBall (g.center i) r ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall (hrg.trans g.radius_outer)).trans (g.outer_inside i)
  have hkernel : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0 := by
    obtain ⟨w,ψ,_,hk,_,_⟩ := hj.2.2.2.1
    exact hk
  have hp := Packet06PlaceModeHotspots.place_mode_hotspots (rounded n hn g η hη j) (z j) (v j)
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j)
    (fun x hx => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j x hx).ne')
    hkernel hj.2.2.2.2 hj.1 hj.2.1 Q hj.2.2.1 target htarget a
    (Packet07PlanarCenters.planeEmbed_coord p) zbase hbase hclose (body g j) hb g.center r M B hball hhotj
  have hgeom := Packet06PlacedClusterBalls.placed_balls g P p rp target hrp htarget hpatch zbase (z j)
    hbase hj.1 hclose hcluster r hr hrg
  have hsminle : smin ≤ s := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*zbase.re) hj.1).mpr
    have hh := (abs_lt.mp hclose).2
    nlinarith
  have hrad : r/s ≤ ρ := (div_le_iff₀ hs).mpr
    (hrρ.trans (mul_le_mul_of_nonneg_left hsminle hρ.le))
  have hmat (x : Space) : 1 ≤ MaterialMaxwell.dielectric (placedCoefficient s a (rounded n hn g η hη j)) x ∧
      MaterialMaxwell.dielectric (placedCoefficient s a (rounded n hn g η hη j)) x ≤ K^2 :=
    Packet06BoundedModalMaterial.placed_bounds _ K
      (fun y => Packet06BoundedModalMaterial.rounded_bounds n hn g η hη K hK hceil j y) s a x
  refine ⟨j,hextra,hs,div_pos hr hs,hrad,hp.2.1,hp.2.2.1,hp.2.2.2.1,hmat,hp.2.2.2.2.1,
    hj.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1,hp.2.2.2.2.2.2.2.1,
    hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2,hs,mul_nonneg (scale_pos s hs).le hB,?_,?_,?_,hp.2.2.2.2.2.2.2.2⟩
  · exact (placement s hs a).isOpenMap _ hb
  · exact Packet06PlacedSmoothBoundary.smooth_boundary_image s hs a (body g j) hsmooth
  · intro i
    exact Packet06PlacedActualCollar.placed_collar (rounded n hn g η hη j)
      (Packet05RoundedModeSupport.rounded_support n hn g η hη j)
      (fun x hx => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j x hx).ne')
      (z j) (v j) hkernel hj.2.2.2.2 s hs a (g.center i) r B (A i)
      (hA i).1 (hA i).2.1 (hA i).2.2 (hcollarj i)

end OQ14.Packet06CollaredHotspotSelection
#print axioms OQ14.Packet06CollaredHotspotSelection.select_placed_collared_hotspots

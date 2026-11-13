import Packet06ActualPeakFamily
import Packet06PhysicalVolumeLimits
import Packet06BoundedModalMaterial

/-! Actual rounded-mode maximum vectors and their physical volume limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06RoundedVolumeLimits
open MeasureTheory Metric Set Filter Maxwell Packet06ConcreteModalGeometry
  Packet06ConcreteModalRounding Packet05BinaryPhaseMaximum Packet05ActualMaximum
open scoped Topology
abbrev Space := Maxwell.Space

structure MaximumData where
  inside : Fin 3 → Space → ℂ
  outside : Fin 3 → Space → ℂ
  side : Bool
  point : Space

def vector (d : MaximumData) : Fin 3 → ℂ := fun k => phaseField d.inside d.outside d.side k d.point

def Valid {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℂ) (v : Packet06SectorOperator.Sector) (j : ℕ) (i : Fin N) (r : ℝ) (d : MaximumData) : Prop :=
  let K := closedBall (g.center i) r
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) v)
    (DynamicVolume.source (rounded n hn g η hη j) v)
  (∀ k, ContinuousOn (d.inside k) (K ∩ closure (body g j))) ∧
  (∀ k, ContinuousOn (d.outside k) (K ∩ closure (closure (body g j))ᶜ)) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (K ∩ body g j)] d.inside k) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (K ∩ (closure (body g j))ᶜ)] d.outside k) ∧
  d.point ∈ K ∩ phaseDomain (body g j) d.side ∧
  ∀ b y, y ∈ K ∩ phaseDomain (body g j) b →
    physicalAmplitude (phaseField d.inside d.outside b) y ≤ physicalAmplitude (phaseField d.inside d.outside d.side) d.point

theorem actual_rounded_maximum_volume {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hm : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrg : r ≤ g.radius)
    (hp : ∀ M : ℝ, ∀ᶠ j in atTop, 0 < (volume.restrict (closedBall (g.center i) r))
      {x | M < physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x})
    (K : ℝ) (hK : 1 < K) (hceil : (1+η)*n^2 ≤ K^2) :
    ∃ d : ℕ → MaximumData,
      (∀ᶠ j in atTop, Valid n hn g η hη (z j) (v j) j i r (d j)) ∧
      Tendsto (fun j => Packet06PhysicalVolumeLimits.amplitude (vector (d j))) atTop atTop ∧
      Tendsto (fun j => 1/(MaterialMaxwell.dielectric (rounded n hn g η hη j) (d j).point *
        (Packet06PhysicalVolumeLimits.amplitude (vector (d j)))^2)) atTop (𝓝 0) ∧
      ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, vector (d (φ j)) k ≠ 0) ∧
        Tendsto (fun j => (((MaterialMaxwell.dielectric (rounded n hn g η hη (φ j)) (d (φ j)).point : ℝ) : ℂ)*
          (vector (d (φ j)) k)^2)⁻¹) atTop (𝓝 0) := by
  classical
  let S := closedBall (g.center i) r
  have hS : S ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall (hrg.trans g.radius_outer)).trans (g.outer_inside i)
  have hmax := Packet05RoundedModeMaximum.eventually_attained_maxima n hn g η hη
  have hvalid : ∀ᶠ j in atTop, ∃ d : MaximumData, Valid n hn g η hη (z j) (v j) j i r d := by
    filter_upwards [hmax,hz,hm,hp 0] with j hj hjz hjm hjp
    obtain ⟨a,b,ha,hb,hae,hbe,hatt⟩ := hj (z j) hjz (v j) hjm S (isCompact_closedBall _ _)
      ⟨g.center i, mem_closedBall_self hr.le⟩ hS
    obtain ⟨side,x,hx,_,hmaxx⟩ := hatt 0 hjp
    exact ⟨⟨a,b,side,x⟩,ha,hb,hae,hbe,hx,hmaxx⟩
  let d : ℕ → MaximumData := fun j => if h : ∃ d, Valid n hn g η hη (z j) (v j) j i r d then Classical.choose h else ⟨0,0,false,0⟩
  have hd : ∀ᶠ j in atTop, Valid n hn g η hη (z j) (v j) j i r (d j) := by
    filter_upwards [hvalid] with j hj
    simp only [d, dif_pos hj]
    exact Classical.choose_spec hj
  have hdiv : Tendsto (fun j => Packet06PhysicalVolumeLimits.amplitude (vector (d j))) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    filter_upwards [hp M,hd,Packet05RoundedModeMaterial.eventually_boundary_certificate g] with j hjp hdj hc
    have hnull : volume (frontier (body g j)) = 0 :=
      Packet07BoundaryNull.bounded_regular_body_boundary_null (body g j) 0 1
        ((body_inside g j).trans ball_subset_closedBall) hc
    have hb : IsOpen (body g j) := CommonBinaryInterface.body_open
      (fun _ => g.datum) (fun _ => g.radius) g.center j
    obtain ⟨hinc,houtc,hin,hout,hpoint,hmaximum⟩ := hdj
    let E := Packet06ComplexElectric.electric (z j)
      (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
      (DynamicVolume.source (rounded n hn g η hη j) (v j))
    have h := Packet07PeakAttainment.positive_volume_exceeds_maximum S (isCompact_closedBall _ _).isClosed.measurableSet
      (phaseDomain (body g j)) (fun b => physicalAmplitude (phaseField (d j).inside (d j).outside b))
      (physicalAmplitude (fun k x => E x k))
      (actual_amplitude_ae (body g j) S hb (isCompact_closedBall _ _).isClosed.measurableSet hnull E
        (d j).inside (d j).outside hin hout)
      (d j).side (d j).point hmaximum M hjp
    simpa [Packet06PhysicalVolumeLimits.amplitude, vector, physicalAmplitude] using h.le
  have hvol := Packet06PhysicalVolumeLimits.physical_and_directional_volumes (fun j => vector (d j))
    (fun j => MaterialMaxwell.dielectric (rounded n hn g η hη j) (d j).point) hdiv
    (fun j => (Packet06BoundedModalMaterial.rounded_bounds n hn g η hη K hK hceil j _).1)
  exact ⟨d,hd,hdiv,hvol.1,hvol.2⟩
end OQ14.Packet06RoundedVolumeLimits
#print axioms OQ14.Packet06RoundedVolumeLimits.actual_rounded_maximum_volume

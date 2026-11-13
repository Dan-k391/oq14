import Packet06RoundedVolumeLimits

/-! Maximum branches are selected on a larger compact ball, so their
restrictions retain the genuine one-sided traces at the smaller ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06StrongRoundedMaximum
open MeasureTheory Metric Set Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits
open scoped Topology
abbrev Space := Maxwell.Space

def StrongValid {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℂ) (v : Packet06SectorOperator.Sector) (j : ℕ) (i : Fin N) (r : ℝ) (d : MaximumData) : Prop :=
  Valid n hn g η hη z v j i r d ∧
  let K := closedBall (g.center i) g.radius
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) v)
    (DynamicVolume.source (rounded n hn g η hη j) v)
  (∀ k, ContinuousOn (d.inside k) (K ∩ closure (body g j))) ∧
  (∀ k, ContinuousOn (d.outside k) (K ∩ closure (closure (body g j))ᶜ)) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (K ∩ body g j)] d.inside k) ∧
  (∀ k, (fun y => E y k) =ᵐ[volume.restrict (K ∩ (closure (body g j))ᶜ)] d.outside k)

theorem strong_maximum_family {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hm : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrg : r < g.radius)
    (hp : ∀ M : ℝ, ∀ᶠ j in atTop, 0 < (volume.restrict (closedBall (g.center i) r))
      {x | M < physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x}) :
    ∃ d : ℕ → MaximumData,
      (∀ᶠ j in atTop, StrongValid n hn g η hη (z j) (v j) j i r (d j)) ∧
      Tendsto (fun j => Packet06PhysicalVolumeLimits.amplitude (vector (d j))) atTop atTop := by
  classical
  let K := closedBall (g.center i) g.radius
  let S := closedBall (g.center i) r
  have hK : K ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  have hSK : S ⊆ K := closedBall_subset_closedBall hrg.le
  have hvalid : ∀ᶠ j in atTop, ∃ d : MaximumData, StrongValid n hn g η hη (z j) (v j) j i r d := by
    filter_upwards [Packet05RoundedCompactBranches.eventually_compact_branches n hn g η hη,hz,hm] with j hj hjz hjm
    obtain ⟨a,b,ha,hb,hae,hbe⟩ := hj (z j) hjz (v j) hjm K (isCompact_closedBall _ _) hK
    have hcont (p : Bool) : ContinuousOn (physicalAmplitude (phaseField a b p)) (S ∩ phaseDomain (body g j) p) := by
      cases p with
      | false => exact amplitude_continuousOn b _ (fun k => (hb k).mono (inter_subset_inter_left _ hSK))
      | true => exact amplitude_continuousOn a _ (fun k => (ha k).mono (inter_subset_inter_left _ hSK))
    obtain ⟨side,x,hx,hmax⟩ := Packet05FiniteBranchMaximum.finite_closed_branches_attain_max S
      (isCompact_closedBall _ _) ⟨g.center i,mem_closedBall_self hr.le⟩ (phaseDomain (body g j))
      (fun p => by cases p <;> exact isClosed_closure) (phase_domains_cover (body g j) S)
      (fun p => physicalAmplitude (phaseField a b p)) hcont
    refine ⟨⟨a,b,side,x⟩,?_,ha,hb,hae,hbe⟩
    exact ⟨fun k => (ha k).mono (inter_subset_inter_left _ hSK),
      fun k => (hb k).mono (inter_subset_inter_left _ hSK),
      fun k => ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hSK) (hae k),
      fun k => ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hSK) (hbe k),hx,hmax⟩
  let d : ℕ → MaximumData := fun j => if h : ∃ d, StrongValid n hn g η hη (z j) (v j) j i r d then Classical.choose h else ⟨0,0,false,0⟩
  have hd : ∀ᶠ j in atTop, StrongValid n hn g η hη (z j) (v j) j i r (d j) := by
    filter_upwards [hvalid] with j hj
    simp only [d, dif_pos hj]
    exact Classical.choose_spec hj
  refine ⟨d,hd,?_⟩
  apply Filter.tendsto_atTop.mpr
  intro M
  filter_upwards [hp M,hd,Packet05RoundedModeMaterial.eventually_boundary_certificate g] with j hjp hdj hc
  have hnull : volume (frontier (body g j)) = 0 :=
    Packet07BoundaryNull.bounded_regular_body_boundary_null (body g j) 0 1
      ((body_inside g j).trans ball_subset_closedBall) hc
  have hb : IsOpen (body g j) := CommonBinaryInterface.body_open
    (fun _ => g.datum) (fun _ => g.radius) g.center j
  obtain ⟨hinc,houtc,hin,hout,hpoint,hmaximum⟩ := hdj.1
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
end OQ14.Packet06StrongRoundedMaximum
#print axioms OQ14.Packet06StrongRoundedMaximum.strong_maximum_family

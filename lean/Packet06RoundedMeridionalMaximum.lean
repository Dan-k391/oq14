import Packet06RoundedBranchSymmetry
import Packet05RoundedModeMaximum
import Packet07MeridionalMaximum

/-! Actual rounded-mode one-sided maxima on an axial observation ball can
be attained on the meridian that becomes the required observation plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedMeridionalMaximum
open MeasureTheory Set Filter Metric Maxwell ModalAxialRotation Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06ConcreteModalRounding Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

def MeridionalAbove (c : StaticCoefficient.Coefficient) (z : ℂ)
    (v : VectorFourier.VectorL2) (B K : Set Space) (M : ℝ) : Prop :=
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c v)
    (DynamicVolume.source c v)
  ∃ inside outside : Fin 3 → Space → ℂ,
    (∀ i, ContinuousOn (inside i) (K ∩ closure B)) ∧
    (∀ i, ContinuousOn (outside i) (K ∩ closure (closure B)ᶜ)) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ B)] inside i) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure B)ᶜ)] outside i) ∧
    ∃ b x, x ∈ K ∩ phaseDomain B b ∧ x 1=0 ∧
      M < physicalAmplitude (phaseField inside outside b) x ∧
      ∀ b' y, y ∈ K ∩ phaseDomain B b' →
        physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x

theorem eventually_meridional_maximum {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ j : ℕ in atTop, ∀ (z : ℂ), z ≠ 0 → ∀ (u : Packet06SectorOperator.Sector),
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 u=0 →
      ∀ (i : Fin N) (r : ℝ), 0 < r → r < g.radius → ∀ M : ℝ,
      let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) u)
        (DynamicVolume.source (rounded n hn g η hη j) u)
      0 < (volume.restrict (closedBall (g.center i) r)) {y | M < physicalAmplitude (fun k x => E x k) y} →
      MeridionalAbove (rounded n hn g η hη j) z u (body g j) (closedBall (g.center i) r) M := by
  filter_upwards [Packet05RoundedCompactBranches.eventually_compact_branches n hn g η hη,
    Packet05RoundedModeMaterial.eventually_boundary_certificate g]
    with j hj hcert z hz u hu i r hr hrb M E hpeak
  let K := closedBall (g.center i) r
  let L := closedBall (g.center i) g.radius
  let V := ball (g.center i) g.radius
  have hL : L ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  have hKL : K ⊆ L := closedBall_subset_closedBall hrb.le
  have hKV : K ⊆ V := closedBall_subset_ball hrb
  obtain ⟨inside,outside,hi,ho,hiae,hoae⟩ := hj z hz u hu L (isCompact_closedBall _ _) hL
  have hic (k : Fin 3) : ContinuousOn (inside k) (K ∩ closure (body g j)) :=
    (hi k).mono (inter_subset_inter_left _ hKL)
  have hoc (k : Fin 3) : ContinuousOn (outside k) (K ∩ closure (closure (body g j))ᶜ) :=
    (ho k).mono (inter_subset_inter_left _ hKL)
  have hiAE (k : Fin 3) : (fun y => Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) u)
        (DynamicVolume.source (rounded n hn g η hη j) u) y k)
      =ᵐ[volume.restrict (K ∩ body g j)] inside k :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hKL) (hiae k)
  have hoAE (k : Fin 3) : (fun y => Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) u)
        (DynamicVolume.source (rounded n hn g η hη j) u) y k)
      =ᵐ[volume.restrict (K ∩ (closure (body g j))ᶜ)] outside k :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hKL) (hoae k)
  have hc (b : Bool) : ContinuousOn (physicalAmplitude (phaseField inside outside b))
      (K ∩ phaseDomain (body g j) b) := by
    cases b
    · exact amplitude_continuousOn _ _ hoc
    · exact amplitude_continuousOn _ _ hic
  have hs (θ : ℝ) (b : Bool) (x : Space) (hx : x ∈ K ∩ phaseDomain (body g j) b) :
      physicalAmplitude (phaseField inside outside b) (spatial θ x)=physicalAmplitude (phaseField inside outside b) x := by
    apply branch_symmetry n hn g η hη j z u hu L V isOpen_ball ball_subset_closedBall
      (ball_subset_closedBall.trans hL)
      (fun t y hy => (Packet06RoundedPhaseRotation.ball_rotation g i g.radius t y).mpr hy)
      b (phaseField inside outside b) _ _ θ x ⟨hKV hx.1,hx.2⟩
    · cases b
      · exact ho
      · exact hi
    · cases b
      · exact hoae
      · exact hiae
  obtain ⟨b,x,hx,hplane,hmax⟩ := Packet07MeridionalMaximum.finite_branches_meridional_maximum
    K (isCompact_closedBall _ _) (nonempty_closedBall.mpr hr.le)
    (phaseDomain (body g j)) (fun b => by cases b <;> exact isClosed_closure)
    (phase_domains_cover (body g j) K) (fun b => physicalAmplitude (phaseField inside outside b)) hc
    (fun θ b x hx => ⟨(Packet06RoundedPhaseRotation.closedBall_rotation g i r θ x).mpr hx.1,
      (Packet06RoundedPhaseRotation.phase_rotation g j b θ x).mpr hx.2⟩) hs
  have hnull : volume (frontier (body g j))=0 :=
    Packet07BoundaryNull.bounded_regular_body_boundary_null (body g j) 0 1
      ((body_inside g j).trans ball_subset_closedBall) hcert
  have hb : IsOpen (body g j) := CommonBinaryInterface.body_open
    (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hhigh := Packet07PeakAttainment.positive_volume_exceeds_maximum K measurableSet_closedBall
    (phaseDomain (body g j)) (fun b => physicalAmplitude (phaseField inside outside b)) _
    (actual_amplitude_ae (body g j) K hb measurableSet_closedBall hnull _ inside outside hiAE hoAE)
    b x hmax M hpeak
  exact ⟨inside,outside,hic,hoc,hiAE,hoAE,b,x,hx,hplane,hhigh,hmax⟩

end OQ14.Packet06RoundedMeridionalMaximum
#print axioms OQ14.Packet06RoundedMeridionalMaximum.eventually_meridional_maximum

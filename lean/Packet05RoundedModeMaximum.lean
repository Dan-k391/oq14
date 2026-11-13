import Packet05BinaryPhaseMaximum
import Packet07BoundaryNull

/-! Actual rounded modes attain their one-sided physical amplitude maxima on
compact observation sets; positive-volume peaks force these maxima to be high. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RoundedModeMaximum
open MeasureTheory Set Filter Metric Maxwell Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_attained_maxima {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ j : ℕ in atTop, ∀ (z : ℂ), z ≠ 0 → ∀ (mode : VectorFourier.VectorL2),
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 mode=0 →
      ∀ (K : Set Space), IsCompact K → K.Nonempty → K ⊆ ball (0 : Space) 1 →
      let E := Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) mode)
        (DynamicVolume.source (rounded n hn g η hη j) mode)
      ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ i, ContinuousOn (inside i) (K ∩ closure (body g j))) ∧
        (∀ i, ContinuousOn (outside i) (K ∩ closure (closure (body g j))ᶜ)) ∧
        (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body g j)] inside i) ∧
        (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure (body g j))ᶜ)] outside i) ∧
        ∀ M : ℝ, 0 < (volume.restrict K) {y | M < physicalAmplitude (fun i x => E x i) y} →
        ∃ b x, x ∈ K ∩ phaseDomain (body g j) b ∧
          M < physicalAmplitude (phaseField inside outside b) x ∧
          ∀ b' y, y ∈ K ∩ phaseDomain (body g j) b' →
            physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x := by
  filter_upwards [Packet05RoundedCompactBranches.eventually_compact_branches n hn g η hη,
    Packet05RoundedModeMaterial.eventually_boundary_certificate g]
    with j hj hcert z hz mode hmode K hK hne hKΩ
  obtain ⟨inside,outside,hic,hoc,hiae,hoae⟩ := hj z hz mode hmode K hK hKΩ
  have hnull : volume (frontier (body g j))=0 :=
    Packet07BoundaryNull.bounded_regular_body_boundary_null (body g j) 0 1
      ((body_inside g j).trans ball_subset_closedBall) hcert
  have hbody : IsOpen (body g j) :=
    CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  exact ⟨inside,outside,hic,hoc,hiae,hoae,fun M hpeak =>
    attained_above_peak (body g j) K hbody hK hne hnull _ inside outside hic hoc hiae hoae M hpeak⟩

end OQ14.Packet05RoundedModeMaximum
#print axioms OQ14.Packet05RoundedModeMaximum.eventually_attained_maxima

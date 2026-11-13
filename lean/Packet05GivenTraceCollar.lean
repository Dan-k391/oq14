import Packet05ActualUniformCollar
import Packet05RoundedCompactBranches
import Packet05PhysicalPhaseCollar

/-! The uniform actual modal collar controls both genuine one-sided traces,
including the rounded material interface, for the same late family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05GivenTraceCollar
open MeasureTheory Set Metric Filter Maxwell Packet06ConcreteModalRounding Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

theorem given_uniform_trace_collar {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (i : Fin N) (A : Set Space) (B : ℝ) (hA : IsOpen A) (hAr : A ⊆ ball (g.center i) g.radius)
    (hbound : ∀ᶠ j in atTop, ∀ᵐ y ∂volume.restrict A,
      physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) y ≤ B) :
      ∀ᶠ j in atTop, ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ k, ContinuousOn (inside k) (closedBall (g.center i) g.radius ∩ closure (body g j))) ∧
        (∀ k, ContinuousOn (outside k) (closedBall (g.center i) g.radius ∩ closure (closure (body g j))ᶜ)) ∧
        (∀ k, (fun y => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) =ᵐ[volume.restrict
            (closedBall (g.center i) g.radius ∩ body g j)] inside k) ∧
        (∀ k, (fun y => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) =ᵐ[volume.restrict
            (closedBall (g.center i) g.radius ∩ (closure (body g j))ᶜ)] outside k) ∧
        ∀ phase x, x ∈ A ∩ phaseDomain (body g j) phase →
          physicalAmplitude (phaseField inside outside phase) x ≤ B := by
  have hK : IsCompact (closedBall (g.center i) g.radius) := isCompact_closedBall _ _
  have hKinside : closedBall (g.center i) g.radius ⊆ ball (0 : Space) 1 :=
    (closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)
  have hAK : A ⊆ closedBall (g.center i) g.radius := hAr.trans ball_subset_closedBall
  filter_upwards [hbound,hz,hmode,Packet05RoundedCompactBranches.eventually_compact_branches n hn g η hη] with j hj hzj hmj hbranches
  obtain ⟨inside,outside,hin,hout,hiae,hoae⟩ := hbranches (z j) hzj (v j) hmj _ hK hKinside
  refine ⟨inside,outside,hin,hout,hiae,hoae,?_⟩
  exact Packet05PhysicalPhaseCollar.physical_phase_collar (body g j) (closedBall (g.center i) g.radius) A
    (CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j) hA hAK
    (Packet06ComplexElectric.electric (z j) (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
      (DynamicVolume.source (rounded n hn g η hη j) (v j))) inside outside hin hout hiae hoae B hj

end OQ14.Packet05GivenTraceCollar
#print axioms OQ14.Packet05GivenTraceCollar.given_uniform_trace_collar

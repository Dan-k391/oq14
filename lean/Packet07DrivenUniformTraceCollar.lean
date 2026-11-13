import Packet07DrivenUniformCollar
import Packet07DrivenUniformCompactActual
import Packet05PhysicalPhaseCollar

/-! The uniform actual modal collar controls both genuine one-sided traces,
including the rounded material interface, for the same late family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenUniformTraceCollar
open MeasureTheory Set Metric Filter Maxwell Packet07PlanarSetup Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_uniform_trace_collar {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r < g.radius) :
    ∃ A : Set Space, ∃ B : ℝ, IsOpen A ∧ A ⊆ ball (g.centers i) g.radius ∧
      sphere (g.centers i) r ⊆ A ∧ 0 ≤ B ∧
      ∀ᶠ j in atTop, ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ k, ContinuousOn (inside k) (closedBall (g.centers i) g.radius ∩ closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))) ∧
        (∀ k, ContinuousOn (outside k) (closedBall (g.centers i) g.radius ∩ closure (closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))ᶜ)) ∧
        (∀ k, (fun y => g.electric freq j input y k) =ᵐ[volume.restrict
            (closedBall (g.centers i) g.radius ∩ CommonBinaryInterface.body g.dataFamily g.radii g.centers j)] inside k) ∧
        (∀ k, (fun y => g.electric freq j input y k) =ᵐ[volume.restrict
            (closedBall (g.centers i) g.radius ∩ (closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))ᶜ)] outside k) ∧
        ∀ phase x, x ∈ A ∩ phaseDomain (CommonBinaryInterface.body g.dataFamily g.radii g.centers j) phase →
          physicalAmplitude (phaseField inside outside phase) x ≤ B := by
  obtain ⟨A,B,hA,hAr,hSphere,hB,hbound⟩ := Packet07DrivenUniformCollar.actual_uniform_collar
    g freq hfreq0 input hfreq i r hr hrR
  have hK : IsCompact (closedBall (g.centers i) g.radius) := isCompact_closedBall _ _
  have hAK : A ⊆ closedBall (g.centers i) g.radius := hAr.trans ball_subset_closedBall
  refine ⟨A,B,hA,hAr,hSphere,hB,?_⟩
  filter_upwards [hbound,Packet07DrivenUniformCompactActual.eventually_compact_branches g freq hfreq0 input hfreq] with j hj hbranches
  obtain ⟨inside,outside,hin,hout,hiae,hoae⟩ := hbranches _ hK
  refine ⟨inside,outside,hin,hout,hiae,hoae,?_⟩
  exact Packet05PhysicalPhaseCollar.physical_phase_collar (CommonBinaryInterface.body g.dataFamily g.radii g.centers j) (closedBall (g.centers i) g.radius) A
    (CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j) hA hAK
    (g.electric freq j input) inside outside hin hout hiae hoae B hj

end OQ14.Packet07DrivenUniformTraceCollar
#print axioms OQ14.Packet07DrivenUniformTraceCollar.actual_uniform_trace_collar

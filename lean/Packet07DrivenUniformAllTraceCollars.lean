import Packet07DrivenUniformTraceCollar

/-! All requested modal collars and their one-sided trace bounds hold for
one common late rounded-family index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformAllTraceCollars
open MeasureTheory Set Metric Filter Maxwell Packet07PlanarSetup Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

theorem all_uniform_trace_collars {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < g.radius) :
    ∃ (A : Fin N → Set Space) (B : Fin N → ℝ),
      (∀ i, IsOpen (A i) ∧ A i ⊆ ball (g.centers i) g.radius ∧ sphere (g.centers i) (r i) ⊆ A i ∧ 0 ≤ B i) ∧
      ∀ᶠ j in atTop, ∀ i, ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ k, ContinuousOn (inside k) (closedBall (g.centers i) g.radius ∩ closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))) ∧
        (∀ k, ContinuousOn (outside k) (closedBall (g.centers i) g.radius ∩ closure (closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))ᶜ)) ∧
        (∀ k, (fun y => g.electric freq j input y k) =ᵐ[volume.restrict
            (closedBall (g.centers i) g.radius ∩ CommonBinaryInterface.body g.dataFamily g.radii g.centers j)] inside k) ∧
        (∀ k, (fun y => g.electric freq j input y k) =ᵐ[volume.restrict
            (closedBall (g.centers i) g.radius ∩ (closure (CommonBinaryInterface.body g.dataFamily g.radii g.centers j))ᶜ)] outside k) ∧
        ∀ phase x, x ∈ A i ∩ phaseDomain (CommonBinaryInterface.body g.dataFamily g.radii g.centers j) phase →
          physicalAmplitude (phaseField inside outside phase) x ≤ B i := by
  classical
  have h := fun i => Packet07DrivenUniformTraceCollar.actual_uniform_trace_collar g freq hfreq0 input hfreq i (r i) (hr i) (hrR i)
  choose A B hA hAr hSphere hB hevent using h
  exact ⟨A,B,fun i => ⟨hA i,hAr i,hSphere i,hB i⟩,Filter.eventually_all.mpr hevent⟩

end OQ14.Packet07DrivenUniformAllTraceCollars
#print axioms OQ14.Packet07DrivenUniformAllTraceCollars.all_uniform_trace_collars

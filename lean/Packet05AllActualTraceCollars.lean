import Packet05ActualTraceCollar

/-! All requested modal collars and their one-sided trace bounds hold for
one common late rounded-family index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05AllActualTraceCollars
open MeasureTheory Set Metric Filter Maxwell Packet06ConcreteModalRounding Packet05ActualMaximum
  Packet05BinaryPhaseMaximum Packet06RoundedBranchSymmetry
open scoped Topology
abbrev Space := Maxwell.Space

theorem all_uniform_trace_collars {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (z0 : ℂ) (v0 : Packet06SectorOperator.Sector)
    (hzlim : Tendsto z atTop (𝓝 z0)) (hvlim : Tendsto v atTop (𝓝 v0))
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < g.radius) :
    ∃ (A : Fin N → Set Space) (B : Fin N → ℝ),
      (∀ i, IsOpen (A i) ∧ A i ⊆ ball (g.center i) g.radius ∧ sphere (g.center i) (r i) ⊆ A i ∧ 0 ≤ B i) ∧
      ∀ᶠ j in atTop, ∀ i, ∃ inside outside : Fin 3 → Space → ℂ,
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
        ∀ phase x, x ∈ A i ∩ phaseDomain (body g j) phase →
          physicalAmplitude (phaseField inside outside phase) x ≤ B i := by
  classical
  have h := fun i => Packet05ActualTraceCollar.actual_uniform_trace_collar n hn g η hη z v z0 v0
    hzlim hvlim hz hmode i (r i) (hr i) (hrR i)
  choose A B hA hAr hSphere hB hevent using h
  exact ⟨A,B,fun i => ⟨hA i,hAr i,hSphere i,hB i⟩,Filter.eventually_all.mpr hevent⟩

end OQ14.Packet05AllActualTraceCollars
#print axioms OQ14.Packet05AllActualTraceCollars.all_uniform_trace_collars

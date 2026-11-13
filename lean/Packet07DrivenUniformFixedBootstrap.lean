import Packet07DrivenUniformFamilyBootstrap
import Packet05FiveCutoffLayout
import Packet05ChartMetricData
import Packet05CutoffThirdBound
import Packet05MetricSecondBound

/-! Construct the fixed metric, five nested cutoffs, and actual family
regional bootstrap at a selected point of a fixed collar chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet07DrivenUniformFixedBootstrap
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05RegionalScalarLocalization Packet05RegionalFluxCutoff Packet05ScalarCutoffTransfer
  Packet05ScalarDielectricFlux Packet05GraphSlopeMultiplier Packet07DrivenUniformFiniteAtlas
  Packet07DrivenUniformFields MaxwellCutoffCommutator Packet05MatrixWeakDerivative Packet05NestedChartCutoffs
  Packet05NestedCutoffSupport Packet05FiveNestedCutoffs
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_chart_bootstrap {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) (chart : Chart g)
    (p : Space) (hp : p ∈ chart.flat) :
    ∃ (R : ℝ) (A : Fin 3 → Fin 3 → Test) (q : Packet05FiveNestedCutoffs.Data (ball p R) p)
      (B K W0 Kboot : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 < R ∧ ball p R ⊆ chart.flat ∧ (∀ j k, ContDiff ℝ 3 (A j k).function) ∧
      (∀ x ∈ ball p R, ∀ j k, (A j k).function x =
        (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
          (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ)) ∧
      0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧ 0 ≤ Kboot ∧
      ∀ᶠ j in atTop,
        let u := scalar g k input chart j
        let C := scalarGradient g k input chart B hB j
        let F := graphForcing g k input chart B hB j
        let U := cutScalar q.q0.inner u
        let G := localizedGradient q.q0.inner u C
        let Rf := localizedForcing q.q0.inner A u F chart.jump chart.jump_nonneg
        let D := cutFluxSource q.q0.inner.complexTest.toTest (fun k => flux A C chart.jump chart.jump_nonneg k-F k)
        (∀ k, HasWeakPartial U (G k) k) ∧
        HasWeakDivergence (fun k => flux A G chart.jump chart.jump_nonneg k-Rf k) D ∧
        (∀ᵐ x ∂volume, x ∈ ball p (2*q.q0.r) → D x = 0) ∧ CompactRepresentative U ∧
        (∀ k, CompactRepresentative (Rf k)) ∧ ‖U‖ ≤ Kboot ∧ (∀ k, ‖G k‖ ≤ Kboot) ∧
        (∀ k, ‖Rf k‖ ≤ Kboot) ∧
        (∀ y ∈ ball p R, ∀ l, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          (Packet07DrivenUniformAtlas.outer g) (correction g k input j) l y‖ ≤ W0) ∧
        ∃ R1 : Fin 3 → L2Vector, ∃ R2 : Fin 3 → Fin 3 → L2Vector,
          (∀ i, i ≠ 2 → ∀ k, HasWeakPartial (Rf k) (R1 i k) i) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasWeakPartial (R1 i k) (R2 i t k) t) ∧
          (∀ i, i ≠ 2 → ∀ k, ‖R1 i k‖ ≤ Kboot) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, ‖R2 i t k‖ ≤ Kboot) := by
  obtain ⟨R,hR,hRsub⟩ := Metric.isOpen_iff.mp chart.flat_open p hp
  obtain ⟨q⟩ := Packet05FiveNestedCutoffs.exists_five (ball p R) isOpen_ball p (mem_ball_self hR)
  obtain ⟨A,a,b,M,Bs,hA3,hAg,ha0,hb0,hM0,ha,hb,hM,hBs⟩ :=
    Packet05ChartMetricData.actual_metric_data chart.graph chart.regular chart.compact p R hR.le
  have hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function := fun j k => (hA3 j k).of_le (by decide)
  have hA : ∀ x ∈ ball p R, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ) :=
    fun x hx => hAg x (ball_subset_closedBall hx)
  obtain ⟨c,hc0,hc⟩ := Packet05MetricSecondBound.matrix_second_bound A hA2
  obtain ⟨τb,hτb0,hτb⟩ := q.q0.derivative_bound
  have hκc2 : ContDiff ℝ 2 q.q0.inner.complexTest.function :=
    complex_regular q.q0.inner 2 (q.q0.regular 2).2.2
  have hκc3 : ContDiff ℝ 3 q.q0.inner.complexTest.function :=
    complex_regular q.q0.inner 3 (q.q0.regular 3).2.2
  obtain ⟨α,β,γ,hα0,hβ0,hγ0,hα,hβ,hγ⟩ :=
    Packet05CutoffSecondBound.derivative_bounds q.q0.inner.complexTest.toTest hκc2
  obtain ⟨ξ,hξ0,hξ⟩ := Packet05CutoffThirdBound.third_derivative_bound q.q0.inner.complexTest.toTest hκc2 hκc3
  have hmetricτ : ∀ x ∈ tsupport q.q0.middle.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ) := fun x hx => hA x (middle_support q.q0 hx)
  have hθΩ : tsupport q.q0.outer.complexTest.function ⊆ ball p R := by
    simpa only [complex_support] using q.q0.outer_support
  have hτa : ∀ x, ‖q.q0.middle.complexTest.function x‖ ≤ 1 := fun x => (q.q0.value_bound x).2.1
  have hτb' : ∀ j x, ‖dcoord q.q0.middle.complexTest.function x j‖ ≤ τb := fun j x => (hτb j x).2.1
  have hτS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < q.q0.r → ∀ x ∈ tsupport q.q0.middle.function,
      x ∈ ball p (8*q.q0.r) ∧ x+h • basis t ∈ ball p (8*q.q0.r) :=
    fun t _ h hh x hx => q.q0.shifted_support t h hh x hx
  obtain ⟨B,K,W0,hB,hB0,hK0,hW00,hboot⟩ :=
    Packet07DrivenUniformFamilyBootstrap.actual_chart_family_bootstrap g k hk0 input hk chart
      A hA2 hA3 (ball p R) (ball p (8*q.q0.r)) (ball p (4*q.q0.r)) (ball p (2*q.q0.r)) hRsub hA
      q.q0.outer.complexTest.toTest hθΩ q.q0.outer_one q.q0.middle q.q0.middle_one q.q0.r q.q0.positive hτS
      b hb M hM Bs hBs hmetricτ a 1 τb ha hτa hτb' q.q0.inner (q.q0.regular 2).2.2 (q.q0.regular 3).2.2
      q.q0.inner_support q.q0.inner_middle q.q0.inner_one c α β γ ξ (fun i t j k x => hc j k i t x) hα hβ hγ hξ
  let Kboot := Packet05RegionalBootstrapCeiling.ceiling (3*K) K chart.jump b M a 1 τb α β γ ξ K K K c
  refine ⟨R,A,q,B,K,W0,Kboot,hB,hR,hRsub,hA3,hA,hB0,hK0,hW00,?_,hboot⟩
  exact Packet05RegionalBootstrapCeiling.ceiling_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end OQ14.Packet07DrivenUniformFixedBootstrap
#print axioms OQ14.Packet07DrivenUniformFixedBootstrap.fixed_chart_bootstrap

import Packet05ActualChartFields

/-! Named actual chart fields satisfy one eventual uniform scalar/forcing
input package, including the physical correction bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05ActualNamedUniformInputs
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05GraphSlopeMultiplier Packet05ScalarDielectricFlux
  Packet05FiniteFixedAtlas Packet06ConcreteModalRounding Packet05ActualChartFields
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_named_uniform_inputs {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (Ω : Set Space) (hΩ : Ω ⊆ chart.flat) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ Ω, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ)) :
    ∃ (B K W0 : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧
      ∀ᶠ j in atTop,
        let u := scalar n hn g η hη z v chart j
        let C := scalarGradient n hn g η hη z v chart B hB j
        let F := graphForcing n hn g η hη z v chart B hB j
        CompactRepresentative u ∧ (∀ k, HasWeakPartial u (C k) k) ∧
        HasDivergenceOn Ω (fun k => flux A C chart.jump chart.jump_nonneg k-F k) 0 ∧
        ‖u‖ ≤ K ∧ (∑ k : Fin 3, ‖C k‖) ≤ 3*K ∧
        (∀ y ∈ Ω, ∀ k, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          Packet05FixedCollarAtlas.outer (correction n hn g η hη z v j) k y‖ ≤ W0) ∧
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ k, CompactRepresentative (F k)) ∧
          (∀ k, k ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 k l) k) ∧
          (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ l, HasWeakPartial (F1 k l) (F2 k t l) t) ∧
          (∑ k : Fin 3, ‖F k‖) ≤ K ∧
          (∀ k, (∑ l : Fin 3, ‖F1 k l‖) ≤ K) ∧
          (∀ k t, (∑ l : Fin 3, ‖F2 k t l‖) ≤ K) := by
  simpa only [scalar,scalarGradient,graphForcing,graphCorrection,potential,correction] using
    Packet05ActualChartUniformInputs.actual_chart_uniform_inputs n hn g η hη chart z v z0 v0 hzlim hvlim hz hmode Ω hΩ A hA

end OQ14.Packet05ActualNamedUniformInputs
#print axioms OQ14.Packet05ActualNamedUniformInputs.actual_named_uniform_inputs

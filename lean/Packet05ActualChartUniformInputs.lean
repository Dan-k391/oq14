import Packet05FixedSubchartEquation
import Packet05FixedChartUniformForcing
import Packet05FixedChartUniformScalar

/-! The actual convergent rounded family has a uniform original scalar and
forcing data envelope on each fixed bounded material subchart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet05ActualChartUniformInputs
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  ConicalGradientGraph Packet05RegionalDivergence Packet05ChartBasis Packet05ChartWeakGradient
  Packet05ChartWeakDivergence Packet05GraphPullback Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05GraphH1Pullback Packet05PhysicalGraphChart Packet05GraphChartMap Packet05FlatWeight
  Packet05ScalarDielectricFlux Packet05FiniteFixedAtlas Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_chart_uniform_inputs {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (W : Set Space) (hW : W ⊆ chart.flat) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ W, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ)) :
    ∃ (B K W0 : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧
      ∀ᶠ j in atTop,
        let c := rounded n hn g η hη j
        let hc := Packet05RoundedModeSupport.rounded_support n hn g η hη j
        let χ := Packet05FixedCollarAtlas.outer
        let U := Packet06ComplexConePotential.potentialData (z j) 1 (StaticCoefficient.sqrtMultiplier c (v j))
          (DynamicVolume.source c (v j)) (DynamicVolume.source_zero c (v j) 1 hc) (StaticNewton.material_source_ae c (v j))
        let Wp := Packet06ComplexPotential.correction (z j) (DynamicVolume.source c (v j))
        let hWp := Packet06ComplexPotential.correction_continuous (z j) 1 (StaticCoefficient.sqrtMultiplier c (v j))
          (DynamicVolume.source c (v j)) (DynamicVolume.source_zero c (v j) 1 hc) (StaticNewton.material_source_ae c (v j))
        let hg : ContDiff ℝ 2 chart.graph := chart.regular.of_le (by decide)
        let u := pullback chart.graph hg.continuous (chartPull chart.up chart.axis (value χ U))
        let C := pulledGradient chart.graph hg (chartVector chart.up chart.axis (gradient χ U)) (fun _ => B) hB
        let Q := chartVector chart.up chart.axis (Packet06ScalarGaussLocalization.correction χ Wp hWp)
        let F : L2Vector := fun k => -mulWeight chart.jump chart.jump_nonneg (transformedFlux chart.graph hg Q (fun _ => B) hB k)
        CompactRepresentative u ∧ (∀ k, HasWeakPartial u (C k) k) ∧
        HasDivergenceOn W (fun k => flux A C chart.jump chart.jump_nonneg k-F k) 0 ∧
        ‖u‖ ≤ K ∧ (∑ k : Fin 3, ‖C k‖) ≤ 3*K ∧
        (∀ y ∈ W, ∀ k, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph χ Wp k y‖ ≤ W0) ∧
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ k, CompactRepresentative (F k)) ∧
          (∀ k, k ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 k l) k) ∧
          (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ l, HasWeakPartial (F1 k l) (F2 k t l) t) ∧
          (∑ k : Fin 3, ‖F k‖) ≤ K ∧
          (∀ k, (∑ l : Fin 3, ‖F1 k l‖) ≤ K) ∧
          (∀ k t, (∑ l : Fin 3, ‖F2 k t l‖) ≤ K) := by
  obtain ⟨B,L1,L2,C,W0,KF,hB,hB0,hL10,hL20,hC0,hW00,hKF,hdi,hdd,hL1,hL2,hforce⟩ :=
    Packet05FixedChartUniformForcing.fixed_chart_uniform_forcing n hn g η hη chart z v z0 v0 hzlim hvlim
  obtain ⟨KC,hKC,hscalar⟩ := Packet05FixedChartUniformScalar.fixed_chart_uniform_scalar n hn g η hη chart z v z0 v0 hzlim hvlim B hB
  let K := max KC KF
  have hK : 0 ≤ K := hKC.trans (le_max_left _ _)
  have hKC' : KC ≤ K := le_max_left _ _
  have hKF' : KF ≤ K := le_max_right _ _
  have heq := Packet05FixedSubchartEquation.eventual_actual_subchart_equation n hn g η hη chart z
    (fun j => (v j : VectorFourier.VectorL2)) hz hmode (fun _ => B) hB hdi hdd W hW A hA
  refine ⟨B,K,W0,hB,hB0,hK,hW00,?_⟩
  filter_upwards [heq] with j hj
  have hs := hscalar j
  have hf := hforce j
  dsimp only at hj hs hf ⊢
  obtain ⟨huc,hgrad,hdiv,_,_⟩ := hj
  obtain ⟨hu,hC⟩ := hs
  obtain ⟨hWp,F1,F2,hFc,hF1,hF2,hFn,hF1n,hF2n⟩ := hf
  refine ⟨huc,hgrad,hdiv,hu.trans hKC',?_,?_,F1,F2,hFc,hF1,hF2,hFn.trans hKF',?_,?_⟩
  · simp only [Fin.sum_univ_three]
    have h0 := (hC 0).trans hKC'
    have h1 := (hC 1).trans hKC'
    have h2 := (hC 2).trans hKC'
    linarith
  · exact fun y hy k => hWp y (hW hy) k
  · exact fun k => (hF1n k).trans hKF'
  · exact fun k t => (hF2n k t).trans hKF'

end OQ14.Packet05ActualChartUniformInputs
#print axioms OQ14.Packet05ActualChartUniformInputs.actual_chart_uniform_inputs

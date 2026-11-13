import Packet07DrivenUniformFields
import Packet07DrivenUniformForcing
import Packet07DrivenUniformHostGraph
import Packet05ChartCorrectionContinuous

/-! Uniform actual original-data inputs on a fixed driven chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet07DrivenUniformNamedInputs
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  ConicalGradientGraph Packet05RegionalDivergence Packet05ChartBasis Packet05ChartWeakGradient
  Packet05ChartWeakDivergence Packet05GraphPullback Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05GraphH1Pullback Packet05PhysicalGraphChart Packet05GraphChartMap Packet05FlatWeight
  Packet05ScalarDielectricFlux Packet07DrivenUniformFiniteAtlas Packet07DrivenUniformFields
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem actual_named_uniform_inputs {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (hk0 : k ≠ 0) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) (chart : Chart g)
    (Ω : Set Space) (hΩ : Ω ⊆ chart.flat) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ Ω, ∀ i j, (A i j).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) i j : ℂ)) :
    ∃ (B K W0 : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧
      ∀ᶠ j in atTop,
        let u := scalar g k input chart j
        let C := scalarGradient g k input chart B hB j
        let F := graphForcing g k input chart B hB j
        CompactRepresentative u ∧ (∀ i, HasWeakPartial u (C i) i) ∧
        HasDivergenceOn Ω (fun i => flux A C chart.jump chart.jump_nonneg i-F i) 0 ∧
        ‖u‖ ≤ K ∧ (∑ i : Fin 3, ‖C i‖) ≤ 3*K ∧
        (∀ y ∈ Ω, ∀ i, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          (Packet07DrivenUniformAtlas.outer g) (correction g k input j) i y‖ ≤ W0) ∧
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ i, CompactRepresentative (F i)) ∧
          (∀ i, i ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 i l) i) ∧
          (∀ i, i ≠ 2 → ∀ m, m ≠ 2 → ∀ l, HasWeakPartial (F1 i l) (F2 i m l) m) ∧
          (∑ i : Fin 3, ‖F i‖) ≤ K ∧ (∀ i, (∑ l : Fin 3, ‖F1 i l‖) ≤ K) ∧
          (∀ i m, (∑ l : Fin 3, ‖F2 i m l‖) ≤ K) := by
  obtain ⟨hW,B,L1,L2,KF,hB,hB0,hL10,hL20,hKF,hdi,hdd,hL1,hL2,hforce⟩ :=
    Packet07DrivenUniformForcing.actual_graph_forcing g k input hk (Packet07DrivenUniformAtlas.outer g)
      chart.graph chart.regular chart.compact chart.up chart.axis chart.jump chart.jump_nonneg
  obtain ⟨KC,hKC,hscalar⟩ := Packet07DrivenUniformGraph.actual_scalar_graph g k input hk
    (Packet07DrivenUniformAtlas.outer g) chart.graph (chart.regular.of_le (by decide)) B hB chart.up chart.axis
  obtain ⟨W0,hW0,hpoint⟩ := Packet07DrivenUniformGraph.actual_correction_pointwise g k input hk (Packet07DrivenUniformAtlas.outer g)
  let V : Set Space := {x | inverseOriented chart.up chart.axis x ∈ ball (0 : Space) (Packet07DrivenUniformAtlas.outer g).rIn}
  obtain ⟨_,hgraph⟩ := Packet07DrivenUniformHostGraph.actual_host_driven_graph g k hk0 input hk chart.body chart.host
    chart.host_ne chart.jump chart.jump_nonneg (Packet07DrivenUniformAtlas.outer g) chart.up chart.axis
    chart.graph (chart.regular.of_le (by decide)) V Ω (fun _ h => h)
    (fun x hx => chart.maps_outer x (hΩ hx)) (fun x hx => chart.side x (hΩ hx))
    (fun _ => B) hB hdi hdd A hA
  let K := max KC KF
  have hK : 0 ≤ K := hKC.trans (le_max_left _ _)
  refine ⟨B,K,W0,hB,hB0,hK,hW0,?_⟩
  filter_upwards [chart.material] with j hj
  have hm := hgraph j (fun x hx => hj x (hΩ hx))
  have hs := hscalar j
  have hf := hforce j
  dsimp only [scalar,scalarGradient,graphForcing,graphCorrection,potential,correction,support] at hm hs hf ⊢
  obtain ⟨huc,hgrad,hdiv,_,_⟩ := hm
  obtain ⟨hu,hC⟩ := hs
  obtain ⟨F1,F2,hFc,hF1,hF2,hFn,hF1n,hF2n⟩ := hf
  refine ⟨huc,hgrad,hdiv,hu.trans (le_max_left _ _),?_,?_,F1,F2,hFc,hF1,hF2,hFn.trans (le_max_right _ _),?_,?_⟩
  · simp only [Fin.sum_univ_three]
    have h0 := (hC 0).trans (le_max_left KC KF)
    have h1 := (hC 1).trans (le_max_left KC KF)
    have h2 := (hC 2).trans (le_max_left KC KF)
    linarith
  · intro y hy i
    let x := inverseOriented chart.up chart.axis (graphMap (liftedHeight chart.graph) y)
    have hx := chart.maps_outer y (hΩ hy)
    have hx1 : Packet07DrivenUniformAtlas.outer g x = 1 :=
      (Packet07DrivenUniformAtlas.outer g).one_of_mem_closedBall (ball_subset_closedBall hx)
    have hp := hpoint j (Equiv.swap chart.axis 2 i) x hx1
    change ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
      (Packet07DrivenUniformAtlas.outer g) (correction g k input j) i y‖ ≤ W0
    simp only [Packet05ChartCorrectionContinuous.chartCorrection, norm_mul, Packet05ChartH2Uniform.chart_sign_norm, one_mul]
    have hbump : ‖bump (Packet07DrivenUniformAtlas.outer g) x‖ ≤ 1 := by simp [bump,hx1]
    exact (mul_le_mul_of_nonneg_right hbump (norm_nonneg _)).trans (by simpa [correction] using hp)
  · exact fun i => (hF1n i).trans (le_max_right _ _)
  · exact fun i m => (hF2n i m).trans (le_max_right _ _)
end OQ14.Packet07DrivenUniformNamedInputs
#print axioms OQ14.Packet07DrivenUniformNamedInputs.actual_named_uniform_inputs

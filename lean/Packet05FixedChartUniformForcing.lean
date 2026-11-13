import Packet05FixedChartActualEquation
import Packet05RoundedActualCorrection
import Packet05ChartH2Uniform
import Packet05UniformGraphForcing
import Packet05SlopeUniformBounds
import Packet05ChartCorrectionBound

/-! Actual rounded modes provide fixed-chart correction and graph-forcing
ceilings uniformly across the entire convergent family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet05FixedChartUniformForcing
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  ConicalGradientGraph Packet05ChartWeakDivergence Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05PhysicalGraphChart Packet05FlatWeight Packet05FiniteFixedAtlas Packet06ConcreteModalRounding Packet05ChartBasis
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_chart_uniform_forcing {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hz : Tendsto z atTop (𝓝 z0)) (hv : Tendsto v atTop (𝓝 v0)) :
    ∃ (B L1 L2 C W0 KF : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 ≤ B ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧ 0 ≤ C ∧ 0 ≤ W0 ∧ 0 ≤ KF ∧
      (∀ i j, MemLp (fun x => dcoord (slopeC chart.graph i) x j) ⊤ volume) ∧
      (∀ i j k, MemLp (fun x => dcoord (fun y => dcoord (slopeC chart.graph i) y j) x k) ⊤ volume) ∧
      (∀ i j x, ‖dcoord (slopeC chart.graph i) x j‖ ≤ L1) ∧
      (∀ i j k x, ‖dcoord (fun y => dcoord (slopeC chart.graph i) y j) x k‖ ≤ L2) ∧
      ∀ j : ℕ,
        let P := Packet05RoundedActualCorrection.actualCorrection n hn g η hη z v Packet05FixedCollarAtlas.outer j
        let Q := chartVector chart.up chart.axis P
        let hg : ContDiff ℝ 2 chart.graph := chart.regular.of_le (by decide)
        let F : L2Vector := fun k => -mulWeight chart.jump chart.jump_nonneg (transformedFlux chart.graph hg Q (fun _ => B) hB k)
        (∀ y ∈ chart.flat, ∀ k, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          Packet05FixedCollarAtlas.outer (Packet06ComplexPotential.correction (z j)
            (DynamicVolume.source (rounded n hn g η hη j) (v j))) k y‖ ≤ W0) ∧
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ k, CompactRepresentative (F k)) ∧
          (∀ k, k ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 k l) k) ∧
          (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ l, HasWeakPartial (F1 k l) (F2 k t l) t) ∧
          (∑ k : Fin 3, ‖F k‖) ≤ KF ∧
          (∀ k, (∑ l : Fin 3, ‖F1 k l‖) ≤ KF) ∧
          (∀ k t, (∑ l : Fin 3, ‖F2 k t l‖) ≤ KF) := by
  classical
  obtain ⟨B,L1,L2,hB0,hL10,hL20,hB,hL1,hL2⟩ :=
    Packet05SlopeUniformBounds.slope_uniform_bounds chart.graph (chart.regular.of_le (by decide)) chart.compact
  obtain ⟨_,hdi,hdd⟩ := Packet05GraphSlopeBounds.slope_bounds chart.graph (chart.regular.of_le (by decide)) chart.compact
  obtain ⟨C,hC,hcorr⟩ := Packet05RoundedActualCorrection.rounded_actual_correction n hn g η hη z v z0 v0 hz hv Packet05FixedCollarAtlas.outer
  let W0 := 10*Packet05ExplicitAnisotropicBound.universalConstant*C
  let K0 := 3*(1+chart.jump)*(1+3*B)*C
  let K1 := 3*(1+chart.jump)*((1+B)+3*(B*(1+B)+L1))*C
  let K2 := 3*(1+chart.jump)*(((1+B)^2+L1)+3*(B*((1+B)^2+L1)+2*L1*(1+B)+L2))*C
  let KF := max K0 (max K1 K2)
  have hU : 0 ≤ Packet05ExplicitAnisotropicBound.universalConstant := by
    unfold Packet05ExplicitAnisotropicBound.universalConstant
    positivity
  have hW0 : 0 ≤ W0 := by dsimp [W0]; positivity
  have hdn : 0 ≤ chart.jump := chart.jump_nonneg
  have hKF : 0 ≤ KF := by dsimp [KF,K0,K1,K2]; positivity
  refine ⟨B,L1,L2,C,W0,KF,hB,hB0,hL10,hL20,hC,hW0,hKF,hdi,hdd,hL1,hL2,?_⟩
  intro j
  dsimp only
  let P := Packet05RoundedActualCorrection.actualCorrection n hn g η hη z v Packet05FixedCollarAtlas.outer j
  have hPcompact (k : Fin 3) : CompactRepresentative (P k) := by
    let W := Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j))
    let hW := Packet06ComplexPotential.correction_continuous (z j) 1
      (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
      (DynamicVolume.source (rounded n hn g η hη j) (v j))
      (DynamicVolume.source_zero (rounded n hn g η hη j) (v j) 1 (Packet05RoundedModeSupport.rounded_support n hn g η hη j))
      (StaticNewton.material_source_ae (rounded n hn g η hη j) (v j))
    refine ⟨fun x => bump Packet05FixedCollarAtlas.outer x*W x k,
      ((Packet05FixedCollarAtlas.outer.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right),?_⟩
    exact Packet06ScalarGaussLocalization.correction_ae Packet05FixedCollarAtlas.outer W hW k
  have hex (k : Fin 3) := hcorr j k
  choose D T hD hT hPn hDn hTn hpoint using hex
  obtain ⟨QG,QH,hQc,hQG,hQH,hQn,hQGn,hQHn⟩ :=
    Packet05ChartH2Uniform.chart_vector_h2_uniform chart.up chart.axis P D T hPcompact hD hT C hPn hDn hTn
  have hforce := Packet05UniformGraphForcing.graph_binary_forcing_uniform chart.graph
    (chart.regular.of_le (by decide)) (chartVector chart.up chart.axis P) QG QH hQc hQG hQH C B L1 L2
    hQn hQGn hQHn hB hdi hdd hL1 hL2 chart.jump chart.jump_nonneg
  obtain ⟨F1,F2,hFc,hF1,hF2,hFn,hF1n,hF2n⟩ := hforce
  constructor
  · intro y hy k
    let x := inverseOriented chart.up chart.axis (Packet05GraphChartMap.graphMap (liftedHeight chart.graph) y)
    have hx : x ∈ ball (0 : Space) Packet05FixedCollarAtlas.outer.rIn := chart.maps_outer y hy
    have hx1 : Packet05FixedCollarAtlas.outer x = 1 := Packet05FixedCollarAtlas.outer.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hw : ‖Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j)) x
      (Equiv.swap chart.axis 2 k)‖ ≤ W0 := hpoint _ x hx1
    change ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph Packet05FixedCollarAtlas.outer
      (Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j))) k y‖ ≤ W0
    simp only [Packet05ChartCorrectionContinuous.chartCorrection, norm_mul, Packet05ChartH2Uniform.chart_sign_norm, one_mul]
    have hbump : ‖bump Packet05FixedCollarAtlas.outer x‖ ≤ 1 := by
      simp [bump,hx1]
    exact (mul_le_mul_of_nonneg_right hbump (norm_nonneg _)).trans (by simpa using hw)
  · exact ⟨F1,F2,hFc,hF1,hF2,hFn.trans (le_max_left _ _),
      fun k => (hF1n k).trans ((le_max_left _ _).trans (le_max_right _ _)),
      fun k t => (hF2n k t).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

end OQ14.Packet05FixedChartUniformForcing
#print axioms OQ14.Packet05FixedChartUniformForcing.fixed_chart_uniform_forcing

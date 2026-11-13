import Packet05FixedChartBootstrap
import Packet05UniformTwoDirectionStrongFamily
import Packet05MetricAllBounds
import Packet05SlopeUniformBounds

/-! Complete uniform two-direction scalar iteration for one actual fixed
collar chart, with all metric and cutoff constants chosen before j. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option synthInstance.maxHeartbeats 500000
namespace OQ14.Packet05FixedChartIteration
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05RegionalScalarLocalization Packet05RegionalFluxCutoff
  Packet05ScalarCutoffTransfer Packet05ScalarDielectricFlux Packet05GraphSlopeMultiplier Packet05FiniteFixedAtlas
  Packet06ConcreteModalRounding Packet05ActualChartFields MaxwellCutoffCommutator Packet05MatrixWeakDerivative
  Packet05NestedChartCutoffs Packet05NestedCutoffSupport Packet05FiveNestedCutoffs
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_chart_iteration {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (p : Space) (hp : p ∈ chart.flat)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0) :
    ∃ (R : ℝ) (A : Fin 3 → Fin 3 → Test) (q : Packet05FiveNestedCutoffs.Data (ball p R) p)
      (B K W0 Kboot P Q : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B),
      0 < R ∧ ball p R ⊆ chart.flat ∧ (∀ j k, ContDiff ℝ 3 (A j k).function) ∧
      (∀ x ∈ ball p R, ∀ j k, (A j k).function x =
        (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
          (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ)) ∧
      0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧ 0 ≤ Kboot ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      ∀ᶠ j in atTop,
        let u := scalar n hn g η hη z v chart j
        let C := scalarGradient n hn g η hη z v chart B hB j
        let F := graphForcing n hn g η hη z v chart B hB j
        let U := cutScalar q.q0.inner u
        let G := localizedGradient q.q0.inner u C
        let Rf := localizedForcing q.q0.inner A u F chart.jump chart.jump_nonneg
        let D := cutFluxSource q.q0.inner.complexTest.toTest (fun k => flux A C chart.jump chart.jump_nonneg k-F k)
        (∀ k, HasWeakPartial U (G k) k) ∧
        HasWeakDivergence (fun k => flux A G chart.jump chart.jump_nonneg k-Rf k) D ∧
        (∀ᵐ x ∂volume, x ∈ ball p (2*q.q0.r) → D x = 0) ∧
        (∀ k, ‖G k‖ ≤ Kboot) ∧ (∀ k, ‖Rf k‖ ≤ Kboot) ∧
        (∀ y ∈ ball p R, ∀ k, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          Packet05FixedCollarAtlas.outer (correction n hn g η hη z v j) k y‖ ≤ W0) ∧
        ∃ R1 : Fin 3 → L2Vector, ∃ R2 : Fin 3 → Fin 3 → L2Vector,
          (∀ i, i ≠ 2 → ∀ k, HasWeakPartial (Rf k) (R1 i k) i) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasWeakPartial (R1 i k) (R2 i t k) t) ∧
          (∀ i, i ≠ 2 → ∀ k, ‖R1 i k‖ ≤ Kboot) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, ‖R2 i t k‖ ≤ Kboot) ∧
          ∃ D0 D1 H00 H01 H10 H11 : L2Vector,
            (∀ k, HasPartialOn (ball p (4*q.q1.r)) (G k) (D0 k) 0) ∧
            (∀ k, HasPartialOn (ball p (4*q.q1.r)) (G k) (D1 k) 1) ∧
            (∀ k, HasPartialOn (ball p (2*q.q2.r)) (D0 k) (H00 k) 0) ∧
            (∀ k, HasPartialOn (ball p (2*q.q2.r)) (D0 k) (H01 k) 1) ∧
            (∀ k, HasPartialOn (ball p (2*q.q2.r)) (D1 k) (H10 k) 0) ∧
            (∀ k, HasPartialOn (ball p (2*q.q2.r)) (D1 k) (H11 k) 1) ∧
            (∀ k, HasWeakPartial (cutScalar q.q2.middle (localizedGradient q.q1.inner (G 0) D0 k)) (H00 k) 0) ∧
            (∀ k, HasWeakPartial (cutScalar q.q2.middle (localizedGradient q.q1.inner (G 0) D0 k)) (H01 k) 1) ∧
            (∀ k, HasWeakPartial (cutScalar q.q2.middle (localizedGradient q.q1.inner (G 1) D1 k)) (H10 k) 0) ∧
            (∀ k, HasWeakPartial (cutScalar q.q2.middle (localizedGradient q.q1.inner (G 1) D1 k)) (H11 k) 1) ∧
            (∀ k, ‖D0 k‖ ≤ P ∧ ‖D1 k‖ ≤ P ∧ ‖H00 k‖ ≤ Q ∧ ‖H01 k‖ ≤ Q ∧ ‖H10 k‖ ≤ Q ∧ ‖H11 k‖ ≤ Q) := by
  obtain ⟨R,A,q,B,K,W0,Kboot,hB,hR,hRsub,hA3,hA,hB0,hK0,hW00,hKboot,hboot⟩ :=
    Packet05FixedChartBootstrap.fixed_chart_bootstrap n hn g η hη chart p hp z v z0 v0 hzlim hvlim hz hmode
  have hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function := fun j k => (hA3 j k).of_le (by decide)
  obtain ⟨a,b,c,ha0,hb0,hc0,ha,hb,hc⟩ := Packet05MetricAllBounds.matrix_all_bounds A hA2
  obtain ⟨M,L1,L2,hM0,_,_,hMs,_,_⟩ := Packet05SlopeUniformBounds.slope_uniform_bounds chart.graph (chart.regular.of_le (by decide)) chart.compact
  have hM : ∀ x, |Packet05GraphSlope.slope chart.graph 0 x| ≤ M ∧ |Packet05GraphSlope.slope chart.graph 1 x| ≤ M := by
    intro x
    constructor <;> simpa [slopeC,Complex.norm_real,Real.norm_eq_abs] using hMs _ x
  have hBs : ∀ l : Fin 2, ∀ x, ‖slopeC chart.graph l.castSucc x‖ ≤ M := fun l x => hMs _ x
  obtain ⟨τa,τb,τc,_,_,_,hτa,hτb,hτc⟩ := Packet05CutoffSecondBound.derivative_bounds q.q1.middle.complexTest.toTest
    (complex_regular q.q1.middle 2 (q.q1.regular 2).2.1)
  obtain ⟨κa,κb,κc,_,_,_,hκa,hκb,hκc⟩ := Packet05CutoffSecondBound.derivative_bounds q.q1.inner.complexTest.toTest
    (complex_regular q.q1.inner 2 (q.q1.regular 2).2.2)
  obtain ⟨ζa,ζb,ζc,_,_,_,hζa,hζb,_⟩ := Packet05CutoffSecondBound.derivative_bounds q.q2.middle.complexTest.toTest
    (complex_regular q.q2.middle 2 (q.q2.regular 2).2.1)
  have hq1 : ball p (8*q.q1.r) ⊆ ball p (2*q.q0.r) := ball8_subset q.q1
  have hq2 : ball p (8*q.q2.r) ⊆ ball p (2*q.q1.r) := ball8_subset q.q2
  have hViter : ball p (4*q.q1.r) ⊆ ball p (2*q.q0.r) := small_ball_subset q.q1 4 (by norm_num)
  have hWiter : ball p (2*q.q2.r) ⊆ ball p (4*q.q1.r) :=
    (small_ball_subset q.q2 2 (by norm_num)).trans (ball_subset_ball (by linarith [q.q1.positive]))
  have hq1Ω : ball p (2*q.q0.r) ⊆ ball p R := small_ball_subset q.q0 2 (by norm_num)
  have hq2Ω : ball p (2*q.q1.r) ⊆ ball p R :=
    (ball_subset_ball (show 2*q.q1.r ≤ 4*q.q1.r by linarith [q.q1.positive])).trans (hViter.trans hq1Ω)
  have hmetricτ : ∀ x ∈ tsupport q.q1.middle.function, ∀ j k, (A j k).function x = _ :=
    fun x hx => hA x (hq1Ω (middle_support q.q1 hx))
  have hmetricζ : ∀ x ∈ tsupport q.q2.middle.function, ∀ j k, (A j k).function x = _ :=
    fun x hx => hA x (hq2Ω (middle_support q.q2 hx))
  have hτS : ∀ i, i ≠ 2 → ∀ h : ℝ, |h| < q.q1.r → ∀ x ∈ tsupport q.q1.middle.function,
      x ∈ ball p (2*q.q0.r) ∧ x+h • basis i ∈ ball p (2*q.q0.r) := by
    intro i _ h hh x hx
    obtain ⟨h1,h2⟩ := q.q1.shifted_support i h hh x hx
    exact ⟨hq1 h1,hq1 h2⟩
  have hζS : ∀ i, i ≠ 2 → ∀ h : ℝ, |h| < q.q2.r → ∀ x ∈ tsupport q.q2.middle.function,
      x ∈ ball p (2*q.q1.r) ∧ x+h • basis i ∈ ball p (2*q.q1.r) := by
    intro i _ h hh x hx
    obtain ⟨h1,h2⟩ := q.q2.shifted_support i h hh x hx
    exact ⟨hq2 h1,hq2 h2⟩
  have hκW : ∀ x ∈ ball p (2*q.q2.r), q.q1.inner.function x = 1 :=
    fun x hx => (q.q1.inner_one x (small_ball_subset q.q2 2 (by norm_num) hx)).eq_of_nhds
  have hζW : ∀ x ∈ ball p (2*q.q2.r), q.q2.middle.function x = 1 :=
    fun x hx => q.q2.middle_one x ((ball_subset_ball (show 2*q.q2.r ≤ 4*q.q2.r by linarith [q.q2.positive])) hx)
  let u := fun j => cutScalar q.q0.inner (scalar n hn g η hη z v chart j)
  let C := fun j => localizedGradient q.q0.inner (scalar n hn g η hη z v chart j)
    (scalarGradient n hn g η hη z v chart B hB j)
  let F := fun j => localizedForcing q.q0.inner A (scalar n hn g η hη z v chart j)
    (graphForcing n hn g η hη z v chart B hB j) chart.jump chart.jump_nonneg
  let D := fun j => cutFluxSource q.q0.inner.complexTest.toTest (fun k => flux A (scalarGradient n hn g η hη z v chart B hB j)
    chart.jump chart.jump_nonneg k-graphForcing n hn g η hη z v chart B hB j k)
  have hfamily : ∀ᶠ j in atTop,
      (∀ k, HasWeakPartial (u j) (C j k) k) ∧ HasWeakDivergence (fun k => flux A (C j) chart.jump chart.jump_nonneg k-F j k) (D j) ∧
      (∀ᵐ x ∂volume, x ∈ ball p (2*q.q0.r) → D j x=0) ∧ CompactRepresentative (u j) ∧
      (∀ k, CompactRepresentative (F j k)) ∧ (∀ k, ‖C j k‖ ≤ Kboot) ∧ (∀ k, ‖F j k‖ ≤ Kboot) ∧
      ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
        (∀ i, i ≠ 2 → ∀ k, HasWeakPartial (F j k) (F1 i k) i) ∧
        (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasWeakPartial (F1 i k) (F2 i t k) t) ∧
        (∀ i, i ≠ 2 → ∀ k, ‖F1 i k‖ ≤ Kboot) ∧ (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, ‖F2 i t k‖ ≤ Kboot) := by
    filter_upwards [hboot] with j hj
    dsimp only at hj
    obtain ⟨hg,hd,hd0,hu,hf,_,hCn,hFn,_,F1,F2,hF1,hF2,hF1n,hF2n⟩ := hj
    exact ⟨hg,hd,hd0,hu,hf,hCn,hFn,F1,F2,hF1,hF2,hF1n,hF2n⟩
  have hiter := Packet05UniformTwoDirectionStrongFamily.uniform_two_direction_strong_family
    chart.graph (chart.regular.of_le (by decide)) A hA2 hA3 u D C F chart.jump chart.jump_nonneg
    (ball p (2*q.q0.r)) (ball p (4*q.q1.r)) (ball p (2*q.q1.r)) isOpen_ball hViter
    q.q1.middle (q.q1.regular 2).2.1 q.q1.middle_one q.q1.r q.q1.positive hτS
    q.q1.inner (q.q1.regular 2).2.2 q.q1.inner_middle q.q1.inner_one
    q.q2.middle q.q2.r q.q2.positive hζS b hb M hM (fun _ => M) hBs hmetricτ hmetricζ
    a τa τb ζa ζb ha hτa hτb hζa hζb c τc κa κb κc (fun i t j k x => hc j k i t x)
    hτc hκa hκb hκc Kboot (ball p (2*q.q2.r)) isOpen_ball hWiter hκW hζW hfamily
  let P0 := 3*Real.sqrt (Packet05EnergyEnvelope.envelope (3*Kboot) (3*Kboot) chart.jump b M a τa τb)+9*τb*Kboot
  let Q0 := Real.sqrt (Packet05EnergyEnvelope.envelope
    (Packet05SecondEnvelope.gradient (3*Kboot) (3*Kboot) chart.jump b M a τa τb κa κb)
    (Packet05SecondEnvelope.forcing (3*Kboot) (3*Kboot) (3*Kboot) (3*Kboot) (3*Kboot) chart.jump b a c τa τb τc κa κb κc M)
    chart.jump b M a ζa ζb)+3*ζb*(Packet05SecondEnvelope.gradient (3*Kboot) (3*Kboot) chart.jump b M a τa τb κa κb)
  let P := max P0 0
  let Q := max Q0 0
  refine ⟨R,A,q,B,K,W0,Kboot,P,Q,hB,hR,hRsub,hA3,hA,hB0,hK0,hW00,hKboot,le_max_right _ _,le_max_right _ _,?_⟩
  filter_upwards [hboot,hiter] with j hb' hi
  dsimp only at hb' hi ⊢
  obtain ⟨hg,hd,hd0,hu,hf,huN,hGn,hFn,hWn,R1,R2,hR1,hR2,hR1n,hR2n⟩ := hb'
  obtain ⟨D0,D1,H00,H01,H10,H11,hD0w,hD1w,hD0l,hD1l,hH00,hH01,hH10,hH11,hH00w,hH01w,hH10w,hH11w,hP0,hP1,hQ⟩ := hi
  have hτcomplex : ∀ x ∈ ball p (4*q.q1.r), q.q1.middle.complexTest.function x = 1 :=
    fun x hx => real_one_complex q.q1.middle (q.q1.middle_one x hx)
  have hD0grad (k : Fin 3) : HasPartialOn (ball p (4*q.q1.r)) (C j k) (D0 k) 0 :=
    cutoff_partial_on _ q.q1.middle.complexTest.toTest (C j k) (D0 k) 0 hτcomplex (hD0w k)
  have hD1grad (k : Fin 3) : HasPartialOn (ball p (4*q.q1.r)) (C j k) (D1 k) 1 :=
    cutoff_partial_on _ q.q1.middle.complexTest.toTest (C j k) (D1 k) 1 hτcomplex (hD1w k)
  have hD0n (k : Fin 3) : ‖D0 k‖ ≤ P :=
    (Finset.single_le_sum (fun l _ => norm_nonneg (D0 l)) (Finset.mem_univ k)).trans (hP0.trans (le_max_left _ _))
  have hD1n (k : Fin 3) : ‖D1 k‖ ≤ P :=
    (Finset.single_le_sum (fun l _ => norm_nonneg (D1 l)) (Finset.mem_univ k)).trans (hP1.trans (le_max_left _ _))
  refine ⟨hg,hd,hd0,hGn,hFn,hWn,R1,R2,hR1,hR2,hR1n,hR2n,D0,D1,H00,H01,H10,H11,
    hD0grad,hD1grad,hH00,hH01,hH10,hH11,hH00w,hH01w,hH10w,hH11w,?_⟩
  intro k
  obtain ⟨h00,h01,h10,h11⟩ := hQ k
  exact ⟨hD0n k,hD1n k,h00.trans (le_max_left _ _),h01.trans (le_max_left _ _),
    h10.trans (le_max_left _ _),h11.trans (le_max_left _ _)⟩

end OQ14.Packet05FixedChartIteration
#print axioms OQ14.Packet05FixedChartIteration.fixed_chart_iteration

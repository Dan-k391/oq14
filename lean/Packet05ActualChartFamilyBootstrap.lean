import Packet05ActualNamedUniformInputs
import Packet05RegionalFamilyChosenBootstrap

/-! Actual rounded modes have a single uniform noncircular scalar bootstrap
on each fixed collar chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet05ActualChartFamilyBootstrap
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalDivergence Packet05RegionalScalarLocalization Packet05RegionalFluxCutoff Packet05ScalarCutoffTransfer
  Packet05ScalarDielectricFlux Packet05GraphSlopeMultiplier Packet05FiniteFixedAtlas Packet06ConcreteModalRounding
  Packet05ActualChartFields MaxwellCutoffCommutator Packet05MatrixWeakDerivative
open scoped Topology
abbrev Space := Maxwell.Space

theorem actual_chart_family_bootstrap {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (Ω S₀ V S : Set Space) (hΩ : Ω ⊆ chart.flat)
    (hA : ∀ x ∈ Ω, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ))
    (θ : Test) (hθΩ : tsupport θ.function ⊆ Ω)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (τ : RealTest univ) (hτV : ∀ x ∈ V, τ.function x = 1) (δ : ℝ) (hδ : 0 < δ)
    (hτS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function,
      x ∈ S₀ ∧ x+h • basis t ∈ S₀)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |Packet05GraphSlope.slope chart.graph 0 x| ≤ M ∧
      |Packet05GraphSlope.slope chart.graph 1 x| ≤ M)
    (Bs : Fin 2 → ℝ) (hBs : ∀ l x, ‖slopeC chart.graph l.castSucc x‖ ≤ Bs l)
    (hmetric : ∀ x ∈ tsupport τ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope chart.graph 0 x)
        (Packet05GraphSlope.slope chart.graph 1 x) j k : ℂ))
    (a τa τb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hτa : ∀ x, ‖τ.complexTest.function x‖ ≤ τa) (hτb : ∀ j x, ‖dcoord τ.complexTest.function x j‖ ≤ τb)
    (κ : RealTest univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκ3 : ContDiff ℝ 3 κ.function)
    (hκΩ : tsupport κ.function ⊆ Ω) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) (c α β γ ξ : ℝ)
    (hc : ∀ i t j k x, ‖dcoord (derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hα : ∀ x, ‖κ.complexTest.function x‖ ≤ α) (hβ : ∀ i x, ‖dcoord κ.complexTest.function x i‖ ≤ β)
    (hγ : ∀ i t x, ‖dcoord (derivativeCutoff κ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hκ2) i).function x t‖ ≤ γ)
    (hξ : ∀ k i t x, ‖dcoord (derivativeCutoff
      (derivativeCutoff κ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hκ2) k)
      (by have hh : ContDiff ℝ 2 (fderiv ℝ κ.complexTest.function) :=
          (contDiff_succ_iff_fderiv (n := 2)).mp (Complex.ofRealCLM.contDiff.comp hκ3) |>.2.2
          exact hh.clm_apply contDiff_const) i).function x t‖ ≤ ξ) :
    ∃ (B K W0 : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B), 0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ W0 ∧
      let Kboot := Packet05RegionalBootstrapCeiling.ceiling (3*K) K chart.jump b M a τa τb α β γ ξ K K K c
      ∀ᶠ j in atTop,
        let u := scalar n hn g η hη z v chart j
        let C := scalarGradient n hn g η hη z v chart B hB j
        let F := graphForcing n hn g η hη z v chart B hB j
        let U := cutScalar κ u
        let G := localizedGradient κ u C
        let R := localizedForcing κ A u F chart.jump chart.jump_nonneg
        let D := cutFluxSource κ.complexTest.toTest (fun k => flux A C chart.jump chart.jump_nonneg k-F k)
        (∀ k, HasWeakPartial U (G k) k) ∧
        HasWeakDivergence (fun k => flux A G chart.jump chart.jump_nonneg k-R k) D ∧
        (∀ᵐ x ∂volume, x ∈ S → D x = 0) ∧ CompactRepresentative U ∧
        (∀ k, CompactRepresentative (R k)) ∧ ‖U‖ ≤ Kboot ∧ (∀ k, ‖G k‖ ≤ Kboot) ∧
        (∀ k, ‖R k‖ ≤ Kboot) ∧
        (∀ y ∈ Ω, ∀ k, ‖Packet05ChartCorrectionContinuous.chartCorrection chart.up chart.axis chart.graph
          Packet05FixedCollarAtlas.outer (correction n hn g η hη z v j) k y‖ ≤ W0) ∧
        ∃ R1 : Fin 3 → L2Vector, ∃ R2 : Fin 3 → Fin 3 → L2Vector,
          (∀ i, i ≠ 2 → ∀ k, HasWeakPartial (R k) (R1 i k) i) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasWeakPartial (R1 i k) (R2 i t k) t) ∧
          (∀ i, i ≠ 2 → ∀ k, ‖R1 i k‖ ≤ Kboot) ∧
          (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, ‖R2 i t k‖ ≤ Kboot) := by
  obtain ⟨B,K,W0,hB,hB0,hK0,hW00,hinputs⟩ :=
    Packet05ActualNamedUniformInputs.actual_named_uniform_inputs n hn g η hη chart z v z0 v0 hzlim hvlim hz hmode Ω hΩ A hA
  let u := scalar n hn g η hη z v chart
  let C := scalarGradient n hn g η hη z v chart B hB
  let F := graphForcing n hn g η hη z v chart B hB
  have hfamily : ∀ᶠ j in atTop, ∃ (F1 : Fin 3 → L2Vector) (F2 : Fin 3 → Fin 3 → L2Vector),
      (∀ k, HasWeakPartial (u j) (C j k) k) ∧ CompactRepresentative (u j) ∧
      (∀ k, CompactRepresentative (F j k)) ∧
      (∀ i, i ≠ 2 → ∀ k, HasWeakPartial (F j k) (F1 i k) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasWeakPartial (F1 i k) (F2 i t k) t) ∧
      HasDivergenceOn Ω (fun k => flux A (C j) chart.jump chart.jump_nonneg k-F j k) 0 ∧
      ‖u j‖ ≤ K ∧ (∑ k : Fin 3, ‖C j k‖) ≤ 3*K ∧ (∑ k : Fin 3, ‖F j k‖) ≤ K ∧
      (∀ i, i ≠ 2 → (∑ k : Fin 3, ‖F1 i k‖) ≤ K) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → (∑ k : Fin 3, ‖F2 i t k‖) ≤ K) := by
    filter_upwards [hinputs] with j hj
    dsimp only at hj
    obtain ⟨hu,hgrad,hdiv,huN,hCN,_,F1,F2,hFc,hF1,hF2,hFN,hF1N,hF2N⟩ := hj
    exact ⟨F1,F2,hgrad,hu,hFc,hF1,hF2,hdiv,huN,hCN,hFN,fun i _ => hF1N i,fun i _ t _ => hF2N i t⟩
  have hboot := Packet05RegionalFamilyChosenBootstrap.regional_family_chosen_bootstrap chart.graph
    (chart.regular.of_le (by decide)) A hA2 hA3 u C F chart.jump chart.jump_nonneg Ω S₀ V S
    θ hθΩ hθS τ hτV δ hδ hτS b hb M hM Bs hBs hmetric a τa τb ha hτa hτb
    κ hκ2 hκ3 hκΩ hκV hκS c α β γ ξ K (3*K) K K K hc hα hβ hγ hξ hfamily
  refine ⟨B,K,W0,hB,hB0,hK0,hW00,?_⟩
  filter_upwards [hboot,hinputs] with j hj hi
  dsimp only at hj hi ⊢
  obtain ⟨hG,hdiv,hD,hUc,hRc,hUn,hGn,hRn,R1,R2,hR1,hR2,hR1n,hR2n⟩ := hj
  exact ⟨hG,hdiv,hD,hUc,hRc,hUn,hGn,hRn,hi.2.2.2.2.2.1,R1,R2,hR1,hR2,hR1n,hR2n⟩

end OQ14.Packet05ActualChartFamilyBootstrap
#print axioms OQ14.Packet05ActualChartFamilyBootstrap.actual_chart_family_bootstrap

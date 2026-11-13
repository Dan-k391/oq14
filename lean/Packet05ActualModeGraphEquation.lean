import Packet05ActualChartSide
import Packet05RegionalBinaryScalarAE
import Packet05OrientedGraphForcing

/-! The actual complex mode, in any oriented physical chart, supplies the
regional binary graph equation and its genuinely regular compact forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05ActualModeGraphEquation
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.ConicalGradientGraph OQ14.Packet05RegionalDivergence
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakGradient OQ14.Packet05ChartWeakDivergence
  OQ14.Packet05ChartH2 OQ14.Packet05ActualOrientedModeScalar OQ14.Packet05ChartBinaryMatch
  OQ14.Packet05GraphPullback OQ14.Packet05GraphPiolaCompact OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05GraphH1Pullback OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05RegionalBinaryScalarAE OQ14.Packet05OrientedGraphForcing
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_mode_graph_equation (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0)
    (S : ℝ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u=0)
    (body : Set Maxwell.Space) (d : ℝ) (hd : 0 ≤ d)
    (hbin : ∀ y : Maxwell.Space, c.value (VectorFourier.coordinateMap y) =
      (by classical exact if y ∈ body then d else 0))
    (χ : ContDiffBump (0 : Maxwell.Space)) (up : Bool) (i : Fin 3)
    (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g) (V W : Set Maxwell.Space)
    (hmapV : ∀ x ∈ V, inverseOriented up i x ∈ ball (0 : Maxwell.Space) χ.rIn)
    (hmapW : ∀ x ∈ W, graphMap (liftedHeight g) x ∈ V)
    (hside : ∀ x ∈ W, inverseOriented up i (graphMap (liftedHeight g) x) ∈ body ↔ 0 < x 2)
    (B : Fin 3 → ℝ) (hB : ∀ j x, ‖slopeC g j x‖ ≤ B j)
    (hdi : ∀ j k, MemLp (fun x => dcoord (slopeC g j) x k) ⊤ volume)
    (hdd : ∀ j k l, MemLp (fun x => dcoord (fun y => dcoord (slopeC g j) y k) x l) ⊤ volume)
    (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ W, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ)) :
    ∃ v : L2Scalar, ∃ C F : L2Vector, ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
      CompactRepresentative v ∧ (∀ j, HasWeakPartial v (C j) j) ∧
      HasDivergenceOn W (fun j => flux A C d hd j-F j) 0 ∧
      (∀ j, CompactRepresentative (F j)) ∧
      (∀ j, ∀ᵐ x ∂volume, F j x =
        -(weight d x * transformedFlux g (hg3.of_le (by decide))
          (chartVector up i (Packet06ScalarGaussLocalization.correction χ
            (Packet06ComplexPotential.correction z (DynamicVolume.source c u))
            (Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
              (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)))) B hB j x)) ∧
      (∀ k, k ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 k j) k) ∧
      (∀ k, k ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 k j) (F2 k t j) t) := by
  let U := Packet06ComplexConePotential.potentialData z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let Wp := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
  let hWp := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let ε := Packet06MaxwellScalarEquation.epsilon c
  let hpε := Packet06MaxwellScalarEquation.epsilon_memLp c
  let v₀ := chartPull up i (value χ U)
  let G := chartVector up i (gradient χ U)
  let Q := chartVector up i (Packet06ScalarGaussLocalization.correction χ Wp hWp)
  let P := chartVector up i (Packet06ScalarGaussLocalization.flux χ U Wp hWp ε hpε)
  let hg := hg3.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  let v := pullback g hg.continuous v₀
  let C := pulledGradient g hg G B hB
  let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)
  have hm := oriented_mode_scalar c z hz S u hc hu χ up i V hmapV
  change CompactRepresentative v₀ ∧ (∀ j, HasWeakPartial v₀ (G j) j) ∧
    HasDivergenceOn V P 0 ∧ (∀ j, (fun x => P j x) =ᵐ[volume] fun x =>
      ε (inverseOriented up i x)*(G j x+Q j x)) ∧
    (∀ j, CompactRepresentative (Q j)) ∧ (∀ j, OQ14.Packet05GraphPiolaH2.HasH2 (Q j)) at hm
  obtain ⟨hvc,hG,hP,hconstit,hQc,hQ2⟩ := hm
  have hP' : ∀ j, ∀ᵐ y ∂volume, y ∈ V → P j y = ε (inverseOriented up i y)*(G j y+Q j y) := by
    intro j
    filter_upwards [hconstit j] with y hy _
    exact hy
  have hmatch := chart_binary_match_ae c body d hbin up i g W hside
  have hregional := regional_binary_scalar_ae g hg V W v₀ G P Q (fun x => ε (inverseOriented up i x))
    hG hP hP' hmapW B hB d hd hmatch A hA
  have hforce := oriented_graph_forcing g hg3 Q hQc hQ2 B hB hdi hdd d hd
  obtain ⟨hFc,F1,F2,hF1,hF2⟩ := hforce
  refine ⟨v,C,F,F1,F2,graph_pullback_compact g hg.continuous v₀ hvc,hregional.1,hregional.2,
    hFc,?_,hF1,hF2⟩
  intro j
  filter_upwards [Lp.coeFn_neg (mulWeight d hd (transformedFlux g hg Q B hB j)),
    mulWeight_ae d hd (transformedFlux g hg Q B hB j)] with x hn hw
  change (-mulWeight d hd (transformedFlux g hg Q B hB j) : L2Scalar) x = _
  rw [hn]
  simp only [Pi.neg_apply,hw]
  rfl

end OQ14.Packet05ActualModeGraphEquation
#print axioms OQ14.Packet05ActualModeGraphEquation.actual_mode_graph_equation

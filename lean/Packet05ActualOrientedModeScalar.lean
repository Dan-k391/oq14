import Packet05ModeCorrectionAdapter
import Packet05ChartConstitutive

/-! Exact complex-mode scalar Gauss data in either signed Cartesian chart:
compact H¹ potential, regional divergence, constitutive relation and compact
H² correction are all derived from the actual volume-kernel mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ActualOrientedModeScalar
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.ConicalGradientGraph OQ14.Packet05RegionalDivergence
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakGradient OQ14.Packet05ChartWeakDivergence
  OQ14.Packet05ChartH2 OQ14.Packet05ChartConstitutive OQ14.Packet05GraphPiolaH2
  OQ14.Packet05ModeCorrectionAdapter

theorem oriented_mode_scalar (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0)
    (S : ℝ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u=0)
    (χ : ContDiffBump (0 : Maxwell.Space)) (up : Bool) (i : Fin 3) (Wchart : Set Maxwell.Space)
    (hmap : ∀ x ∈ Wchart, inverseOriented up i x ∈ ball (0 : Maxwell.Space) χ.rIn) :
    let U := Packet06ComplexConePotential.potentialData z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    let W := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
    let hW := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    let ε := Packet06MaxwellScalarEquation.epsilon c
    let v := chartPull up i (value χ U)
    let G := chartVector up i (gradient χ U)
    let Q := chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW)
    let P := chartVector up i (Packet06ScalarGaussLocalization.flux χ U W hW ε
      (Packet06MaxwellScalarEquation.epsilon_memLp c))
    CompactRepresentative v ∧
    (∀ j, HasWeakPartial v (G j) j) ∧
    HasDivergenceOn Wchart P 0 ∧
    (∀ j, (fun x => P j x) =ᵐ[volume] fun x =>
      ε (inverseOriented up i x)*(G j x+Q j x)) ∧
    (∀ j, CompactRepresentative (Q j)) ∧ (∀ j, HasH2 (Q j)) := by
  dsimp only
  let U := Packet06ComplexConePotential.potentialData z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let W := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
  let hW := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let ε := Packet06MaxwellScalarEquation.epsilon c
  let hε := Packet06MaxwellScalarEquation.epsilon_memLp c
  let G := gradient χ U
  let Q := Packet06ScalarGaussLocalization.correction χ W hW
  let P := Packet06ScalarGaussLocalization.flux χ U W hW ε hε
  have hmode := Packet06MaxwellScalarEquation.actual_scalar_equation c z hz S u hc hu χ
  change CompactRepresentative (value χ U) ∧ (∀ j, HasWeakPartial (value χ U) (G j) j) ∧
    (∀ j, CompactRepresentative (Q j)) ∧ _ ∧ HasDivergenceOn _ P 0 at hmode
  obtain ⟨hv,hG,hQ,_,hP⟩ := hmode
  have hQ2 : ∀ j, HasH2 (Q j) := actual_correction_h2 c z S u hc χ
  have hchartQ := chart_vector_compact_h2 up i Q hQ hQ2
  refine ⟨chart_pull_compact up i _ hv, ?_, ?_, ?_, hchartQ.1, hchartQ.2⟩
  · intro j
    exact chart_weak_partial up i j (value χ U) (G (Equiv.swap i 2 j)) (hG _)
  · have h := chart_regional_divergence up i (ball (0 : Maxwell.Space) χ.rIn) Wchart P 0 hP hmap
    simpa [chartPull] using h
  · intro j
    apply chart_constitutive up i P G Q ε
    intro k
    exact Packet06ScalarGaussLocalization.flux_ae χ U W hW ε hε k

end OQ14.Packet05ActualOrientedModeScalar
#print axioms OQ14.Packet05ActualOrientedModeScalar.oriented_mode_scalar

import Packet07DrivenUniformForcing
import Packet07IncidentScalarEquation
import Packet05ChartConstitutive
import Packet05ChartH2

/-! The actual driven scalar equation in a signed Cartesian chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenUniformOriented
open MeasureTheory Metric Set Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph
  Packet05RegionalDivergence Packet05ChartBasis Packet05ChartWeakGradient Packet05ChartWeakDivergence
  Packet05ChartH2 Packet05ChartConstitutive Packet05GraphPiolaH2
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem oriented_driven_scalar {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (k : ℝ) (hk0 : k ≠ 0) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (χ : ContDiffBump (0 : Space)) (up : Bool) (i : Fin 3) (V : Set Space)
    (hmap : ∀ x ∈ V, inverseOriented up i x ∈ ball (0 : Space) χ.rIn) :
    ∃ hW : ∀ j l, Continuous (fun x => (FiniteAngularHerglotz.incident k input).E x l +
      Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
        (Packet07SelectedRadiation.actualUnknown g k j input)) x l),
    ∀ j,
    let c := g.rounded j
    let u := Packet07SelectedRadiation.actualUnknown g k j input
    let hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
    let U := Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u g.enclosing hc) (StaticNewton.material_source_ae c u)
    let W : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l + Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x l
    let ε := Packet06MaxwellScalarEquation.epsilon c
    let v := chartPull up i (value χ U)
    let G := chartVector up i (gradient χ U)
    let Q := chartVector up i (Packet06ScalarGaussLocalization.correction χ W (hW j))
    let X := chartVector up i (Packet06ScalarGaussLocalization.flux χ U W (hW j) ε (Packet06MaxwellScalarEquation.epsilon_memLp c))
    CompactRepresentative v ∧ (∀ l, HasWeakPartial v (G l) l) ∧
    HasDivergenceOn V X 0 ∧
    (∀ l, (fun x => X l x) =ᵐ[volume] fun x => ε (inverseOriented up i x)*(G l x+Q l x)) ∧
    (∀ l, CompactRepresentative (Q l)) ∧ (∀ l, HasH2 (Q l)) ∧
    (∀ l, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
      gradient χ U l x + Packet06ScalarGaussLocalization.correction χ W (hW j) l x = g.electric k j input x l) := by
  obtain ⟨hW,K,hK,hcorr⟩ := Packet07DrivenUniformActual.actual_driven_correction g k input hk χ
  refine ⟨hW,?_⟩
  intro j
  dsimp only
  let c := g.rounded j
  let u := Packet07SelectedRadiation.actualUnknown g k j input
  let hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
  let U := Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u g.enclosing hc) (StaticNewton.material_source_ae c u)
  let W : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l + Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x l
  let ε := Packet06MaxwellScalarEquation.epsilon c
  let hε := Packet06MaxwellScalarEquation.epsilon_memLp c
  let G := gradient χ U
  let Q := Packet06ScalarGaussLocalization.correction χ W (hW j)
  let X := Packet06ScalarGaussLocalization.flux χ U W (hW j) ε hε
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius c g.enclosing :=
    hk.trans (MaterialVolumeLimit.commonRadius_le c d g.enclosing le_rfl)
  obtain ⟨hW',hv,hG,hQ,hfield,hX⟩ := Packet07IncidentScalarEquation.actual_incident_scalar_equation
    c k g.enclosing hk0 g.enclosing_nonnegative hfreq (FiniteAngularHerglotz.incident k input) hc χ
  have hQ2 : ∀ l, HasH2 (Q l) := by
    intro l
    obtain ⟨D,T,hD,hT,_,_,_⟩ := hcorr j l
    exact ⟨D,T,hD,hT⟩
  have hchartQ := chart_vector_compact_h2 up i Q hQ hQ2
  refine ⟨chart_pull_compact up i _ hv,?_,?_,?_,hchartQ.1,hchartQ.2,?_⟩
  · intro l
    exact chart_weak_partial up i l (value χ U) (G (Equiv.swap i 2 l)) (hG _)
  · have h := chart_regional_divergence up i (ball (0 : Space) χ.rIn) V X 0 hX hmap
    simpa [chartPull] using h
  · intro l
    apply chart_constitutive up i X G Q ε
    intro m
    exact Packet06ScalarGaussLocalization.flux_ae χ U W (hW j) ε hε m
  · exact hfield
end OQ14.Packet07DrivenUniformOriented
#print axioms OQ14.Packet07DrivenUniformOriented.oriented_driven_scalar

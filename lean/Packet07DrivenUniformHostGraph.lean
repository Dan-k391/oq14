import Packet07DrivenUniformOriented
import Packet05HostChartMatch

/-! The literal driven field supplies the regional binary graph equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet07DrivenUniformHostGraph
open MeasureTheory Metric Set Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph
  Packet05RegionalDivergence Packet05ChartBasis Packet05ChartWeakGradient Packet05ChartWeakDivergence
  Packet05ChartH2 Packet05HostNormalization Packet05HostChartMatch Packet05GraphPullback Packet05GraphPiolaCompact
  Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence Packet05GraphH1Pullback Packet05PhysicalGraphChart
  Packet05GraphChartMap Packet05FlatWeight Packet05ScalarDielectricFlux Packet05RegionalBinaryScalarAE Packet05OrientedGraphForcing
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem actual_host_driven_graph {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (k : ℝ) (hk0 : k ≠ 0) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (body : Set Space) (host : ℂ) (hhost : host ≠ 0) (jump : ℝ) (hj : 0 ≤ jump)
    (χ : ContDiffBump (0 : Space)) (up : Bool) (axis : Fin 3)
    (f : Plane → ℝ) (hf3 : ContDiff ℝ 3 f) (V W : Set Space)
    (hmapV : ∀ x ∈ V, inverseOriented up axis x ∈ ball (0 : Space) χ.rIn)
    (hmapW : ∀ x ∈ W, graphMap (liftedHeight f) x ∈ V)
    (hside : ∀ x ∈ W, inverseOriented up axis (graphMap (liftedHeight f) x) ∈ body ↔ 0 < x 2)
    (B : Fin 3 → ℝ) (hB : ∀ l x, ‖slopeC f l x‖ ≤ B l)
    (hdi : ∀ l m, MemLp (fun x => dcoord (slopeC f l) x m) ⊤ volume)
    (hdd : ∀ l m n, MemLp (fun x => dcoord (fun y => dcoord (slopeC f l) y m) x n) ⊤ volume)
    (A : Fin 3 → Fin 3 → Test) (hA : ∀ x ∈ W, ∀ l m, (A l m).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope f 0 x) (Packet05GraphSlope.slope f 1 x) l m : ℂ)) :
    ∃ hW : ∀ j l, Continuous (fun x => (FiniteAngularHerglotz.incident k input).E x l +
      Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
        (Packet07SelectedRadiation.actualUnknown g k j input)) x l),
    ∀ j, (∀ x ∈ W, Packet06MaxwellScalarEquation.epsilon (g.rounded j)
      (inverseOriented up axis (graphMap (liftedHeight f) x)) =
        host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight f) x) ∈ body
          then (1+jump : ℂ) else 1)) →
    let c := g.rounded j
    let u := Packet07SelectedRadiation.actualUnknown g k j input
    let hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
    let U := Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u g.enclosing hc) (StaticNewton.material_source_ae c u)
    let Wp : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l + Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x l
    let hf := hf3.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
    let v := pullback f hf.continuous (chartPull up axis (value χ U))
    let C := pulledGradient f hf (chartVector up axis (gradient χ U)) B hB
    let Q := chartVector up axis (Packet06ScalarGaussLocalization.correction χ Wp (hW j))
    let F : L2Vector := fun l => -mulWeight jump hj (transformedFlux f hf Q B hB l)
    CompactRepresentative v ∧ (∀ l, HasWeakPartial v (C l) l) ∧
      HasDivergenceOn W (fun l => flux A C jump hj l-F l) 0 ∧
      (∀ l, CompactRepresentative (F l)) ∧
      ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
        (∀ a, a ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 a l) a) ∧
        (∀ a, a ≠ 2 → ∀ b, b ≠ 2 → ∀ l, HasWeakPartial (F1 a l) (F2 a b l) b) := by
  obtain ⟨hW,horient⟩ := Packet07DrivenUniformOriented.oriented_driven_scalar g k hk0 input hk χ up axis V hmapV
  refine ⟨hW,?_⟩
  intro j hmaterial
  dsimp only
  let c := g.rounded j
  let u := Packet07SelectedRadiation.actualUnknown g k j input
  let hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
  let U := Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u g.enclosing hc) (StaticNewton.material_source_ae c u)
  let Wp : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l + Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x l
  let ε := Packet06MaxwellScalarEquation.epsilon c
  let hpε := Packet06MaxwellScalarEquation.epsilon_memLp c
  let v₀ := chartPull up axis (value χ U)
  let G := chartVector up axis (gradient χ U)
  let Q := chartVector up axis (Packet06ScalarGaussLocalization.correction χ Wp (hW j))
  let X := chartVector up axis (Packet06ScalarGaussLocalization.flux χ U Wp (hW j) ε hpε)
  let X' : L2Vector := fun l => host⁻¹ • X l
  let ε' : Space → ℂ := fun x => host⁻¹*ε (inverseOriented up axis x)
  let hf := hf3.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have hm := horient j
  change CompactRepresentative v₀ ∧ (∀ l, HasWeakPartial v₀ (G l) l) ∧
    HasDivergenceOn V X 0 ∧ (∀ l, (fun x => X l x) =ᵐ[volume] fun x =>
      ε (inverseOriented up axis x)*(G l x+Q l x)) ∧
    (∀ l, CompactRepresentative (Q l)) ∧ (∀ l, Packet05GraphPiolaH2.HasH2 (Q l)) ∧ _ at hm
  obtain ⟨hvc,hG,hX,hconstit,hQc,hQ2,_⟩ := hm
  have hX' : HasDivergenceOn V X' 0 := regional_divergence_smul V X host⁻¹ hX
  have hconstit' : ∀ l, ∀ᵐ x ∂volume, x ∈ V → X' l x = ε' x*(G l x+Q l x) := by
    intro l
    exact normalized_constitutive_ae V X G Q (fun x => ε (inverseOriented up axis x)) host hconstit l
  have hmatch := host_chart_match_ae c body host hhost jump up axis f W hside hmaterial
  have hregional := regional_binary_scalar_ae f hf V W v₀ G X' Q ε'
    hG hX' hconstit' hmapW B hB jump hj hmatch A hA
  have hforce := oriented_graph_forcing f hf3 Q hQc hQ2 B hB hdi hdd jump hj
  exact ⟨graph_pullback_compact f hf.continuous v₀ hvc,hregional.1,hregional.2,hforce⟩
end OQ14.Packet07DrivenUniformHostGraph
#print axioms OQ14.Packet07DrivenUniformHostGraph.actual_host_driven_graph

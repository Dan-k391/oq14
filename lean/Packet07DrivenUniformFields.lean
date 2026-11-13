import Packet07DrivenUniformFiniteAtlas
import Packet07DrivenUniformGraph

/-! Named actual scalar and correction fields on a fixed driven-family chart. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformFields
open MeasureTheory Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph Packet07DrivenUniformFiniteAtlas
  Packet05ChartWeakGradient Packet05ChartWeakDivergence Packet05GraphPullback Packet05GraphH1Pullback
  Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence Packet05FlatWeight
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
abbrev Space := Maxwell.Space
variable {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ} (g : Packet07PlanarSetup.Setup N P d t)
  (k : ℝ) (input : Input)

def support (j : ℕ) := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
  g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j

def potential (j : ℕ) : PotentialData :=
  let c := g.rounded j
  let u := Packet07SelectedRadiation.actualUnknown g k j input
  Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u g.enclosing (support g j)) (StaticNewton.material_source_ae c u)

def correction (j : ℕ) : Field := fun x l => (FiniteAngularHerglotz.incident k input).E x l +
  Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
    (Packet07SelectedRadiation.actualUnknown g k j input)) x l

theorem correction_continuous (j : ℕ) : ∀ l, Continuous (fun x => correction g k input j x l) := by
  intro l
  exact ((FiniteAngularHerglotz.incident k input).smoothE l).continuous.add
    (Packet06ComplexPotential.correction_continuous (k : ℂ) g.enclosing
      (StaticCoefficient.sqrtMultiplier (g.rounded j) (Packet07SelectedRadiation.actualUnknown g k j input))
      (DynamicVolume.source (g.rounded j) (Packet07SelectedRadiation.actualUnknown g k j input))
      (DynamicVolume.source_zero _ _ _ (support g j)) (StaticNewton.material_source_ae _ _) l)

def scalar (chart : Chart g) (j : ℕ) : L2Scalar :=
  pullback chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide)).continuous
    (chartPull chart.up chart.axis (value (Packet07DrivenUniformAtlas.outer g) (potential g k input j)))

def scalarGradient (chart : Chart g) (B : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B) (j : ℕ) : L2Vector :=
  pulledGradient chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide))
    (chartVector chart.up chart.axis (gradient (Packet07DrivenUniformAtlas.outer g) (potential g k input j))) (fun _ => B) hB

def graphCorrection (chart : Chart g) (j : ℕ) : L2Vector :=
  chartVector chart.up chart.axis (Packet06ScalarGaussLocalization.correction (Packet07DrivenUniformAtlas.outer g)
    (correction g k input j) (correction_continuous g k input j))

def graphForcing (chart : Chart g) (B : ℝ) (hB : ∀ i x, ‖slopeC chart.graph i x‖ ≤ B) (j : ℕ) : L2Vector :=
  fun l => -mulWeight chart.jump chart.jump_nonneg
    (transformedFlux chart.graph (chart.regular.of_le (show (2 : WithTop ℕ∞) ≤ 4 by decide))
      (graphCorrection g k input chart j) (fun _ => B) hB l)
end OQ14.Packet07DrivenUniformFields
#print axioms OQ14.Packet07DrivenUniformFields.correction_continuous

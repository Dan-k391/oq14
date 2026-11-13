import Packet07DrivenUniformActual
import Packet05UniformMaterialScalarGraph
import Packet05ContinuousH2Bound

/-! Actual scalar-graph and pointwise correction bounds for fixed illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet07DrivenUniformGraph
open MeasureTheory Set Metric Filter Maxwell WeakCurl ConicalGradientGraph
  Packet05GraphSlopeMultiplier Packet05GraphPullback Packet05ChartWeakGradient
  Packet05ChartWeakDivergence Packet05GraphH1Pullback DivCurlCompact
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

theorem actual_scalar_graph {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (χ : ContDiffBump (0 : Space)) (f : Plane → ℝ) (hf : ContDiff ℝ 2 f)
    (Bs : ℝ) (hBs : ∀ i x, ‖slopeC f i x‖ ≤ Bs) (up : Bool) (axis : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j,
      let u := Packet07SelectedRadiation.actualUnknown g k j input
      let F := StaticCoefficient.sqrtMultiplier (g.rounded j) u
      let ρ := DynamicVolume.source (g.rounded j) u
      let hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
        g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
      let U := Packet06ComplexConePotential.potentialData (k : ℂ) g.enclosing F ρ
        (DynamicVolume.source_zero (g.rounded j) u g.enclosing hc) (StaticNewton.material_source_ae (g.rounded j) u)
      let v := pullback f hf.continuous (chartPull up axis (value χ U))
      let C := pulledGradient f hf (chartVector up axis (ConicalGradientGraph.gradient χ U)) (fun _ => Bs) hBs
      ‖v‖ ≤ K ∧ ∀ i, ‖C i‖ ≤ K := by
  obtain ⟨L,hL,hu⟩ := Packet07DrivenUniformFamily.actual_unknown_bounded g k input hk
  exact Packet05UniformMaterialScalarGraph.material_family_scalar_graph g.rounded (fun _ => (k : ℂ))
    (fun j => Packet07SelectedRadiation.actualUnknown g k j input) g.enclosing ‖(k : ℂ)‖ d L Bs
    g.enclosing_nonnegative (norm_nonneg _) hL
    (ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed)
    (fun _ => le_rfl) (fun _ => le_rfl) hu χ f hf hBs up axis

theorem actual_correction_pointwise {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (χ : ContDiffBump (0 : Space)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j i x, χ x=1 →
      ‖(FiniteAngularHerglotz.incident k input).E x i +
        Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
          (Packet07SelectedRadiation.actualUnknown g k j input)) x i‖ ≤ K := by
  obtain ⟨hW,K,hK,hall⟩ := Packet07DrivenUniformActual.actual_driven_correction g k input hk χ
  refine ⟨10*Packet05ExplicitAnisotropicBound.universalConstant*K,by
    unfold Packet05ExplicitAnisotropicBound.universalConstant; positivity,?_⟩
  intro j i x hx
  obtain ⟨D,T,hD,hT,hu,hd,ht⟩ := hall j i
  let W := fun y : Space => (FiniteAngularHerglotz.incident k input).E y i +
    Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
      (Packet07SelectedRadiation.actualUnknown g k j input)) y i
  have hc : HasCompactSupport (fun y => ConicalGradientGraph.bump χ y*W y) :=
    (χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right
  have hcont : Continuous (fun y => ConicalGradientGraph.bump χ y*W y) :=
    (Complex.continuous_ofReal.comp χ.continuous).mul (hW j i)
  have h := Packet05ContinuousH2Bound.continuous_h2_bound _ _ hcont hc
    (Packet06ScalarGaussLocalization.correction_ae χ _ (hW j) i) D T hD hT K hu hd ht x
  simpa only [ConicalGradientGraph.bump,hx,Complex.ofReal_one,one_mul,W] using h
end OQ14.Packet07DrivenUniformGraph
#print axioms OQ14.Packet07DrivenUniformGraph.actual_scalar_graph
#print axioms OQ14.Packet07DrivenUniformGraph.actual_correction_pointwise

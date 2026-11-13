import Packet07SelectedRadiation
import Packet07DrivenUniformCorrection
import MaterialVolumeLimit

/-! Convergence and a common norm bound for the literal driven unknowns. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet07DrivenUniformFamily
open MeasureTheory Set Metric Filter Maxwell
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem actual_unknown_tendsto {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) :
    let c₀ := ConicalCommonMaterial.coefficient g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep
    let F := ConicalBallExtension.vector g.enclosing
      (ConicalEntireGauge.restricted g.enclosing (FiniteAngularHerglotz.incident k input))
    Tendsto (fun j => Packet07SelectedRadiation.actualUnknown g k j input) atTop
      (𝓝 (MaterialVolumeLimit.weightedSolution c₀ k g.enclosing F)) := by
  dsimp only
  have he := CommonBinaryRounding.coefficient_eventually_eq g.dataFamily g.radii g.centers d
    g.contrast_pos.le g.contrast_bound g.radii_outer g.outer_sep g.radii_pos
  have ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (g.rounded j).value x) atTop
      (𝓝 ((ConicalCommonMaterial.coefficient g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep).value x)) := by
    filter_upwards [he] with x hx
    exact tendsto_const_nhds.congr' (hx.mono (fun _ h => h.symm))
  have h := MaterialVolumeLimit.weightedSolution_tendsto g.rounded
    (ConicalCommonMaterial.coefficient g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep) d k g.enclosing g.enclosing_nonnegative
    (fun _ => le_rfl) le_rfl ha hk
    (ConicalBallExtension.vector g.enclosing
      (ConicalEntireGauge.restricted g.enclosing (FiniteAngularHerglotz.incident k input)))
  simpa only [Packet07SelectedRadiation.actualUnknown,ConicalMaterialRunge.solutionOperator,
    ConicalBallExtension.weighted,MaterialVolumeLimit.weightedSolution,ContinuousLinearMap.comp_apply] using h

theorem actual_unknown_bounded {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j, ‖Packet07SelectedRadiation.actualUnknown g k j input‖ ≤ L := by
  obtain ⟨L,hL,hb⟩ := (Metric.isBounded_range_of_tendsto _ (actual_unknown_tendsto g k input hk)).exists_pos_norm_le
  exact ⟨L,hL.le,fun j => hb _ (mem_range_self j)⟩
end OQ14.Packet07DrivenUniformFamily
#print axioms OQ14.Packet07DrivenUniformFamily.actual_unknown_tendsto
#print axioms OQ14.Packet07DrivenUniformFamily.actual_unknown_bounded

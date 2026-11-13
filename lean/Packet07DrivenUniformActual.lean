import Packet07DrivenUniformFamily

/-! Uniform actual correction for the same literal rounded driven sequence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet07DrivenUniformActual
open MeasureTheory Set Metric Filter Maxwell WeakCurl WeakPoynting DivCurlCompact
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
abbrev Space := Maxwell.Space

theorem actual_driven_correction {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (χ : ContDiffBump (0 : Space)) :
    let W : ℕ → Field := fun j x i => (FiniteAngularHerglotz.incident k input).E x i +
      Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
        (Packet07SelectedRadiation.actualUnknown g k j input)) x i
    ∃ hW : ∀ j i, Continuous (fun x => W j x i),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j l,
      ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial (Packet06ScalarGaussLocalization.correction χ (W j) (hW j) l) (D i) i) ∧
        (∀ i m, HasWeakPartial (D i) (T i m) m) ∧
        ‖Packet06ScalarGaussLocalization.correction χ (W j) (hW j) l‖ ≤ K ∧
        (∀ i, ‖D i‖ ≤ K) ∧ (∀ i m, ‖T i m‖ ≤ K) := by
  obtain ⟨L,hL,hu⟩ := Packet07DrivenUniformFamily.actual_unknown_bounded g k input hk
  exact Packet07DrivenUniformCorrection.driven_correction g.rounded (fun _ => (k : ℂ))
    (fun j => Packet07SelectedRadiation.actualUnknown g k j input) (χ.rOut+1) g.enclosing ‖(k : ℂ)‖ d L
    (by linarith [χ.rOut_pos]) g.enclosing_nonnegative (norm_nonneg _) hL
    (ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed)
    (fun _ => le_rfl) (fun _ => le_rfl) hu χ (by linarith)
    (FiniteAngularHerglotz.incident k input).E (FiniteAngularHerglotz.incident k input).smoothE
end OQ14.Packet07DrivenUniformActual
#print axioms OQ14.Packet07DrivenUniformActual.actual_driven_correction

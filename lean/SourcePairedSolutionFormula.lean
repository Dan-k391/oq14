import SourcePairedSmallness

/-! The explicit solution formula of the combined paired-shell-plus-inclusion volume equation. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace OQ14.SourcePairedSolutionFormula
open Filter Topology Metric MeasureTheory
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

theorem combined_solution_eq (q : ℝ) (hq : 1≤q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x)=0)
    (hE : IsUnit (DynamicVolume.volumeBlock ci 1 b-
      ShellInclusionReaction.reaction (SourcePairedInclusion.shell q hq n r) ci 1
        (SourcePairedInclusion.data q hq n r).X))
    (f : VectorL2) :
    MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
        (SourcePairedInclusion.data q hq n r).X f=
      ShellInclusionBlocks.combinedInverse
        (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r))
        (StaticCoefficient.sqrtMultiplier ci)
        (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X) f := by
  have hs : IsUnit (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X) := SourcePairedInclusion.shell_isUnit q hq n r
  have hd : ShellInclusionVolume.Disjoint (SourcePairedInclusion.shell q hq n r) ci :=
    SourcePairedInclusion.disjoint q hq n r ci b hb hci
  have hEff : IsUnit (ShellInclusionBlocks.effective
      (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r))
      (StaticCoefficient.sqrtMultiplier ci)
      (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X)) := by
    rw [SourcePairedInclusion.effective_eq q hq n r ci b hb hci]
    exact hE
  exact ShellInclusionVolume.solution_eq (SourcePairedInclusion.shell q hq n r) ci 1
    (SourcePairedInclusion.data q hq n r).X hd hs hEff f

theorem eventually_combined_solution_eq (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0<b) (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb)) :
    ∀ᶠ r : ℕ in atTop, ∀ f : VectorL2,
      MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (SourcePairedInclusion.data q hq n r).X f=
        ShellInclusionBlocks.combinedInverse
          (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r))
          (StaticCoefficient.sqrtMultiplier ci)
          (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X) f := by
  filter_upwards [SourcePairedReduction.eventually_effective_isUnit q hq n ci d b hb hcar hL,
    SourcePairedReduction.eventually_inner_radius q hq n b] with r hE hbR
  intro f
  exact combined_solution_eq q hq n r ci b hbR.le (SourcePairedReduction.inclusion_vanish ci d b hcar) hE f

end OQ14.SourcePairedSolutionFormula
#print axioms OQ14.SourcePairedSolutionFormula.combined_solution_eq
#print axioms OQ14.SourcePairedSolutionFormula.eventually_combined_solution_eq

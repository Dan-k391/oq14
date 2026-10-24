import SourcePairedReduction

/-! Explicit smallness: the limiting clamped paired-core operator is bounded by inclusion data and the
sup norms of the limit kernel entries, so the limiting effective block is a unit for small
inclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace OQ14.SourcePairedSmallness
open Filter Topology Metric MeasureTheory OQ14.ShellInclusionVolume OQ14.ShellInclusionReaction
open OQ14.SourcePairedInclusion OQ14.SourcePairedReduction
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

variable (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0<b)

/-- The sum of the sup norms of the nine limit kernel entries on the core region. -/
def limitKernelNorm : ℝ := ∑ i : Fin 3,∑ j : Fin 3,‖SourcePairedCore.limitMap q hq n b i j‖

theorem limitingOperator_norm_le :
    ‖SourcePairedCore.limitingOperator ci d q hq n b hb‖ ≤
      ci.bound*volume.real d.carrier*limitKernelNorm q hq n b := by
  unfold SourcePairedCore.limitingOperator limitKernelNorm
  exact BoundedMaterialKernel.operator_norm d _

/-- Inclusion-data smallness: dynamic error plus contrast times carrier volume times limit kernel norm. -/
def dataSmallness : ℝ :=
  DynamicVolume.errorBound ci 1 b+ci.bound*volume.real d.carrier*limitKernelNorm q hq n b

theorem limitEffective_isUnit_of_data (hsmall : dataSmallness q hq n ci d b<1) :
    IsUnit (limitEffective q hq n ci d b hb) := by
  apply limitEffective_isUnit_of_small q hq n ci d b hb
  calc DynamicVolume.errorBound ci 1 b+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖
      ≤ DynamicVolume.errorBound ci 1 b+ci.bound*volume.real d.carrier*limitKernelNorm q hq n b :=
        add_le_add le_rfl (limitingOperator_norm_le q hq n ci d b hb)
    _ < 1 := hsmall

variable (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
include hb hcar

theorem eventually_combined_isUnit_of_data (hsmall : dataSmallness q hq n ci d b<1) :
    ∀ᶠ r : ℕ in atTop,IsUnit (DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X) :=
  eventually_combined_isUnit q hq n ci d b hb hcar (limitEffective_isUnit_of_data q hq n ci d b hb hsmall)

end OQ14.SourcePairedSmallness
#print axioms OQ14.SourcePairedSmallness.limitingOperator_norm_le
#print axioms OQ14.SourcePairedSmallness.limitEffective_isUnit_of_data
#print axioms OQ14.SourcePairedSmallness.eventually_combined_isUnit_of_data

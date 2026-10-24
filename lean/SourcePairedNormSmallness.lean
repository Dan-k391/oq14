import SourcePairedSmallness

/-! Unit-ness of the limiting effective inclusion block from operator-norm bounds alone: the dynamic
remainder sandwich norm plus the inclusion-data limit term below one. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
namespace OQ14.SourcePairedNormSmallness
open Filter Topology MeasureTheory OQ14.SourcePairedReduction OQ14.SourcePairedSmallness
abbrev Coefficient := StaticCoefficient.Coefficient

variable (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0<b)

/-- The limiting effective block as a perturbation of the positive static block. -/
theorem limitEffective_eq_perturbation :
    limitEffective q hq n ci d b hb=
      StaticCoefficient.weightedBlock ci-
        (DynamicVolume.weightedRemainder ci 1 b+SourcePairedCore.limitingOperator ci d q hq n b hb) := by
  unfold limitEffective DynamicVolume.volumeBlock
  rw [StaticNewton.volumeBlock_eq]
  abel

/-- Unit-ness from the remainder operator norm and the limit operator norm. -/
theorem limitEffective_isUnit_of_norms
    (hsmall : ‖DynamicVolume.weightedRemainder ci 1 b‖+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖<1) :
    IsUnit (limitEffective q hq n ci d b hb) := by
  rw [limitEffective_eq_perturbation]
  exact StaticCoefficient.weightedBlock_perturbation_isUnit ci _ ((norm_add_le _ _).trans_lt hsmall)

/-- Unit-ness from the remainder operator norm and the inclusion-data limit term. -/
theorem limitEffective_isUnit_of_remainder_norm
    (hsmall : ‖DynamicVolume.weightedRemainder ci 1 b‖+
      ci.bound*volume.real d.carrier*limitKernelNorm q hq n b<1) :
    IsUnit (limitEffective q hq n ci d b hb) := by
  apply limitEffective_isUnit_of_norms q hq n ci d b hb
  calc ‖DynamicVolume.weightedRemainder ci 1 b‖+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖
      ≤ ‖DynamicVolume.weightedRemainder ci 1 b‖+ci.bound*volume.real d.carrier*limitKernelNorm q hq n b :=
        add_le_add le_rfl (limitingOperator_norm_le q hq n ci d b hb)
    _ < 1 := hsmall

/-- Inverse bound of the limiting effective block under the same smallness. -/
theorem limitEffective_inverse_le
    (hsmall : ‖DynamicVolume.weightedRemainder ci 1 b‖+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖<1) :
    ‖Ring.inverse (limitEffective q hq n ci d b hb)‖ ≤
      (1-(‖DynamicVolume.weightedRemainder ci 1 b‖+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖))⁻¹ := by
  rw [limitEffective_eq_perturbation]
  have hQ := norm_add_le (DynamicVolume.weightedRemainder ci 1 b) (SourcePairedCore.limitingOperator ci d q hq n b hb)
  apply (StaticCoefficient.weightedBlock_perturbation_inverse ci _ (hQ.trans_lt hsmall)).trans
  exact inv_anti₀ (by linarith) (by linarith)

end OQ14.SourcePairedNormSmallness
#print axioms OQ14.SourcePairedNormSmallness.limitEffective_eq_perturbation
#print axioms OQ14.SourcePairedNormSmallness.limitEffective_isUnit_of_norms
#print axioms OQ14.SourcePairedNormSmallness.limitEffective_isUnit_of_remainder_norm
#print axioms OQ14.SourcePairedNormSmallness.limitEffective_inverse_le

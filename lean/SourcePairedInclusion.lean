import ShellInclusionTruncation
import SourcePairedTensor

/-! The shell-plus-inclusion block reduction instantiated for the actual finite paired dielectric
shells: disjointness, shell invertibility, and the effective inclusion block with the inclusion's
own radius. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourcePairedInclusion
open Metric OQ14.ShellInclusionVolume OQ14.ShellInclusionReaction OQ14.SourcePairedGeometry
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev Space := Maxwell.Space

variable (q : ℝ) (hq : 1≤q) (n r : ℕ)

/-- The actual paired-shell data at shell index r. -/
abbrev data : SourceRadialSystem.Data := physicalData q (zero_lt_one.trans_le hq) n r

/-- The actual paired-shell susceptibility. -/
abbrev shell : Coefficient := SourcePairedTensor.material q hq n r

include hq in
theorem one_le_sq : 1≤q^2 := by nlinarith

theorem shell_inner (x : Space) (hx : ‖x‖≤(data q hq n r).R) :
    (shell q hq n r).value (VectorFourier.coordinateMap x)=0 :=
  SourceMaterialCoefficient.value_inner _ _ (one_le_sq q hq)
    (physical_material_bounds q (zero_lt_one.trans_le hq) hq n r) x hx

theorem shell_outer (x : Space) (hx : (data q hq n r).X<‖x‖) :
    (shell q hq n r).value (VectorFourier.coordinateMap x)=0 :=
  SourceMaterialCoefficient.value_outer _ _ (one_le_sq q hq)
    (physical_material_bounds q (zero_lt_one.trans_le hq) hq n r) x hx

theorem radii_ordered : (data q hq n r).R≤(data q hq n r).X :=
  RadialStack.chain_ordered (data q hq n r).chain

theorem shell_support (x : Space) (hx : x ∉ closedBall (0 : Space) (data q hq n r).X) :
    (shell q hq n r).value (VectorFourier.coordinateMap x)=0 := by
  apply shell_outer
  simpa only [mem_closedBall,dist_zero_right,not_le] using hx

theorem shell_isUnit : IsUnit (DynamicVolume.volumeBlock (shell q hq n r) 1 (data q hq n r).X) :=
  SourceMaterialPartition.volumeBlock_isUnit _ (q^2) (one_le_sq q hq)
    (physical_material_bounds q (zero_lt_one.trans_le hq) hq n r) 1 (by norm_num)

section Inclusion
variable (ci : Coefficient) (b : ℝ) (hb : b≤(data q hq n r).R)
  (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x)=0)
include hb hci

theorem disjoint : Disjoint (shell q hq n r) ci := by
  intro ξ
  set x := VectorFourier.coordinateMap.symm ξ with hx
  have hξ : ξ=VectorFourier.coordinateMap x := by rw [hx,MeasurableEquiv.apply_symm_apply]
  rw [hξ]
  by_cases h : ‖x‖≤(data q hq n r).R
  · exact Or.inl (shell_inner q hq n r x h)
  · right
    apply hci
    simp only [mem_closedBall,dist_zero_right,not_le] at h ⊢
    exact lt_of_le_of_lt hb h

theorem inclusion_support (x : Space) (hx : x ∉ closedBall (0 : Space) (data q hq n r).X) :
    ci.value (VectorFourier.coordinateMap x)=0 :=
  hci x (fun h => hx (closedBall_subset_closedBall (hb.trans (radii_ordered q hq n r)) h))

/-- The combined paired-shell-plus-inclusion block is the named combined block. -/
theorem combined_eq :
    DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X=
      ShellInclusionBlocks.combined (StaticCoefficient.sqrtMultiplier (shell q hq n r))
        (StaticCoefficient.sqrtMultiplier ci) (kernel 1 (data q hq n r).X) :=
  ShellInclusionVolume.combined_eq _ _ _ _ (disjoint q hq n r ci b hb hci)

/-- The effective inclusion block is the inclusion's own block at radius b minus the paired-shell
reaction operator. -/
theorem effective_eq :
    ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier (shell q hq n r))
        (StaticCoefficient.sqrtMultiplier ci) (kernel 1 (data q hq n r).X)=
      DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X := by
  rw [ShellInclusionReaction.effective_eq,
    ShellInclusionTruncation.volumeBlock_radius_independent ci 1 (data q hq n r).X b
      (inclusion_support q hq n r ci b hb hci) hci]

theorem combined_isUnit_of_effective
    (hE : IsUnit (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X)) :
    IsUnit (DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X) := by
  apply ShellInclusionVolume.combined_isUnit _ _ _ _ (disjoint q hq n r ci b hb hci) (shell_isUnit q hq n r)
  rw [effective_eq q hq n r ci b hb hci]
  exact hE

/-- Every solution of the combined paired-shell-plus-inclusion equation yields a solution of the
effective inclusion equation with the shell-Green datum. -/
theorem effective_of_solution (u f : VectorL2)
    (hu : DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X u=f) :
    (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X)
      (StaticCoefficient.sqrtMultiplier ci (kernel 1 (data q hq n r).X
        ((StaticCoefficient.sqrtMultiplier (shell q hq n r)+StaticCoefficient.sqrtMultiplier ci) u)))=
      StaticCoefficient.sqrtMultiplier ci
        (ShellInclusionAlgebra.green (StaticCoefficient.sqrtMultiplier (shell q hq n r)) (kernel 1 (data q hq n r).X)
          ((StaticCoefficient.sqrtMultiplier (shell q hq n r)+StaticCoefficient.sqrtMultiplier ci) f)) := by
  rw [← effective_eq q hq n r ci b hb hci]
  exact ShellInclusionVolume.effective_of_solution _ _ _ _ (disjoint q hq n r ci b hb hci)
    (shell_isUnit q hq n r) u f hu

/-- Small inclusions inside the actual paired shell make the combined block a unit. -/
theorem combined_isUnit_of_small
    (hsmall : ShellInclusionSmall.smallness (shell q hq n r) ci 1 (data q hq n r).X<1) :
    IsUnit (DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X) :=
  ShellInclusionSmall.combined_isUnit_of_small _ _ _ _ (disjoint q hq n r ci b hb hci) (shell_isUnit q hq n r)
    ((data q hq n r).hR.le.trans (radii_ordered q hq n r)) hsmall

end Inclusion
end OQ14.SourcePairedInclusion
#print axioms OQ14.SourcePairedInclusion.shell_inner
#print axioms OQ14.SourcePairedInclusion.shell_outer
#print axioms OQ14.SourcePairedInclusion.shell_support
#print axioms OQ14.SourcePairedInclusion.shell_isUnit
#print axioms OQ14.SourcePairedInclusion.disjoint
#print axioms OQ14.SourcePairedInclusion.combined_eq
#print axioms OQ14.SourcePairedInclusion.effective_eq
#print axioms OQ14.SourcePairedInclusion.combined_isUnit_of_effective
#print axioms OQ14.SourcePairedInclusion.effective_of_solution
#print axioms OQ14.SourcePairedInclusion.combined_isUnit_of_small

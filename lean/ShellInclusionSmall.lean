import ShellInclusionReaction

/-! Small inclusions inside an invertible shell: norm bounds on the reaction operator and
unit-ness of the effective inclusion block and of the combined block. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ShellInclusionSmall
open OQ14.ShellInclusionVolume OQ14.ShellInclusionReaction
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev Operator := VectorL2 →L[ℂ] VectorL2

variable (cs ci : Coefficient) (k R : ℝ)

theorem sandwich_norm_le (c : Coefficient) (G : Operator) :
    ‖StaticCoefficient.sqrtMultiplier c*G*StaticCoefficient.sqrtMultiplier c‖ ≤ c.bound*‖G‖ := by
  have hS := StaticCoefficient.sqrtMultiplier_norm_le c
  have h1 : ‖StaticCoefficient.sqrtMultiplier c*G*StaticCoefficient.sqrtMultiplier c‖ ≤
      ‖StaticCoefficient.sqrtMultiplier c‖*‖G‖*‖StaticCoefficient.sqrtMultiplier c‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h2 : ‖StaticCoefficient.sqrtMultiplier c‖*‖G‖*‖StaticCoefficient.sqrtMultiplier c‖ ≤
      Real.sqrt c.bound*‖G‖*Real.sqrt c.bound :=
    mul_le_mul (mul_le_mul_of_nonneg_right hS (norm_nonneg _)) hS (norm_nonneg _) (by positivity)
  have h3 : Real.sqrt c.bound*‖G‖*Real.sqrt c.bound=c.bound*‖G‖ := by
    rw [mul_comm (Real.sqrt c.bound*‖G‖) (Real.sqrt c.bound),← mul_assoc,
      Real.mul_self_sqrt (StaticCoefficient.bound_nonnegative c)]
  exact (h1.trans h2).trans_eq h3

theorem reaction_norm_le : ‖reaction cs ci k R‖ ≤ ci.bound*‖scatteredGreen cs k R‖ :=
  sandwich_norm_le ci (scatteredGreen cs k R)

theorem scatteredGreen_norm_le :
    ‖scatteredGreen cs k R‖ ≤ ‖kernel k R‖*(cs.bound*‖Ring.inverse (DynamicVolume.volumeBlock cs k R)‖)*‖kernel k R‖ := by
  unfold scatteredGreen
  have hmid : ‖StaticCoefficient.sqrtMultiplier cs*Ring.inverse (DynamicVolume.volumeBlock cs k R)*
      StaticCoefficient.sqrtMultiplier cs‖ ≤ cs.bound*‖Ring.inverse (DynamicVolume.volumeBlock cs k R)‖ :=
    sandwich_norm_le cs _
  calc ‖kernel k R*StaticCoefficient.sqrtMultiplier cs*Ring.inverse (DynamicVolume.volumeBlock cs k R)*
        StaticCoefficient.sqrtMultiplier cs*kernel k R‖
      = ‖kernel k R*(StaticCoefficient.sqrtMultiplier cs*Ring.inverse (DynamicVolume.volumeBlock cs k R)*
        StaticCoefficient.sqrtMultiplier cs)*kernel k R‖ := by noncomm_ring
    _ ≤ ‖kernel k R*(StaticCoefficient.sqrtMultiplier cs*Ring.inverse (DynamicVolume.volumeBlock cs k R)*
        StaticCoefficient.sqrtMultiplier cs)‖*‖kernel k R‖ := norm_mul_le _ _
    _ ≤ ‖kernel k R‖*‖StaticCoefficient.sqrtMultiplier cs*Ring.inverse (DynamicVolume.volumeBlock cs k R)*
        StaticCoefficient.sqrtMultiplier cs‖*‖kernel k R‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid (norm_nonneg _)) (norm_nonneg _)

/-- The effective inclusion block as a perturbation of the positive static block. -/
theorem effective_eq_perturbation :
    DynamicVolume.volumeBlock ci k R-reaction cs ci k R=
      StaticCoefficient.weightedBlock ci-(DynamicVolume.weightedRemainder ci k R+reaction cs ci k R) := by
  unfold DynamicVolume.volumeBlock
  rw [StaticNewton.volumeBlock_eq]
  abel

/-- Smallness of the inclusion: dynamic error plus contrast times scattered-Green norm below one. -/
def smallness : ℝ := DynamicVolume.errorBound ci k R+ci.bound*‖scatteredGreen cs k R‖

theorem perturbation_norm_le (hR : 0 ≤ R) :
    ‖DynamicVolume.weightedRemainder ci k R+reaction cs ci k R‖ ≤ smallness cs ci k R :=
  (norm_add_le _ _).trans (add_le_add (DynamicVolume.weightedRemainder_norm_le ci k R hR)
    (reaction_norm_le cs ci k R))

theorem effective_isUnit_of_small (hR : 0 ≤ R) (hsmall : smallness cs ci k R<1) :
    IsUnit (DynamicVolume.volumeBlock ci k R-reaction cs ci k R) := by
  rw [effective_eq_perturbation]
  exact StaticCoefficient.weightedBlock_perturbation_isUnit ci _
    ((perturbation_norm_le cs ci k R hR).trans_lt hsmall)

theorem effective_inverse_le (hR : 0 ≤ R) (hsmall : smallness cs ci k R<1) :
    ‖Ring.inverse (DynamicVolume.volumeBlock ci k R-reaction cs ci k R)‖ ≤ (1-smallness cs ci k R)⁻¹ := by
  rw [effective_eq_perturbation]
  have hQ := (perturbation_norm_le cs ci k R hR)
  apply (StaticCoefficient.weightedBlock_perturbation_inverse ci _ (hQ.trans_lt hsmall)).trans
  exact inv_anti₀ (by linarith) (by linarith)

/-- A small inclusion inside an invertible shell: the combined volume block is a unit. -/
theorem combined_isUnit_of_small (h : Disjoint cs ci) (hs : IsUnit (DynamicVolume.volumeBlock cs k R))
    (hR : 0 ≤ R) (hsmall : smallness cs ci k R<1) :
    IsUnit (DynamicVolume.volumeBlock (add cs ci) k R) :=
  combined_isUnit_of_reaction cs ci k R h hs (effective_isUnit_of_small cs ci k R hR hsmall)

end OQ14.ShellInclusionSmall
#print axioms OQ14.ShellInclusionSmall.sandwich_norm_le
#print axioms OQ14.ShellInclusionSmall.reaction_norm_le
#print axioms OQ14.ShellInclusionSmall.scatteredGreen_norm_le
#print axioms OQ14.ShellInclusionSmall.effective_eq_perturbation
#print axioms OQ14.ShellInclusionSmall.perturbation_norm_le
#print axioms OQ14.ShellInclusionSmall.effective_isUnit_of_small
#print axioms OQ14.ShellInclusionSmall.effective_inverse_le
#print axioms OQ14.ShellInclusionSmall.combined_isUnit_of_small

import ShellInclusionVolume

/-! The effective inclusion block is the inclusion's own volume block minus the shell reaction
operator, the inclusion-weighted shell-scattered part of the shell Green operator. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ShellInclusionReaction
open OQ14.ShellInclusionVolume
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev Operator := VectorL2 →L[ℂ] VectorL2

variable (cs ci : Coefficient) (k R : ℝ)

/-- The shell-scattered part of the shell Green operator: `T Ss r Ss T` with `r` the ring inverse
of the shell block. -/
def scatteredGreen : Operator :=
  kernel k R*StaticCoefficient.sqrtMultiplier cs*
    Ring.inverse (DynamicVolume.volumeBlock cs k R)*StaticCoefficient.sqrtMultiplier cs*kernel k R

/-- The inclusion-weighted shell reaction operator. -/
def reaction : Operator :=
  StaticCoefficient.sqrtMultiplier ci*scatteredGreen cs k R*StaticCoefficient.sqrtMultiplier ci

theorem green_eq : ShellInclusionAlgebra.green (StaticCoefficient.sqrtMultiplier cs) (kernel k R)=
    kernel k R+scatteredGreen cs k R := by
  unfold ShellInclusionAlgebra.green scatteredGreen
  rw [shell_eq cs k R]
  rfl

/-- The effective inclusion block equals the inclusion's own dynamic volume block minus the
inclusion-weighted shell reaction operator. -/
theorem effective_eq :
    ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (kernel k R)=
      DynamicVolume.volumeBlock ci k R-reaction cs ci k R := by
  unfold ShellInclusionBlocks.effective reaction
  rw [green_eq,volumeBlock_eq_sandwich ci k R]
  noncomm_ring

/-- The combined block is a unit as soon as the shell block is a unit and the inclusion block
minus the reaction operator is a unit. -/
theorem combined_isUnit_of_reaction (h : Disjoint cs ci)
    (hs : IsUnit (DynamicVolume.volumeBlock cs k R))
    (hE : IsUnit (DynamicVolume.volumeBlock ci k R-reaction cs ci k R)) :
    IsUnit (DynamicVolume.volumeBlock (add cs ci) k R) :=
  combined_isUnit cs ci k R h hs (by rwa [effective_eq])

end OQ14.ShellInclusionReaction
#print axioms OQ14.ShellInclusionReaction.green_eq
#print axioms OQ14.ShellInclusionReaction.effective_eq
#print axioms OQ14.ShellInclusionReaction.combined_isUnit_of_reaction

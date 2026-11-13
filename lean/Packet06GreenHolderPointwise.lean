import Packet06GreenHolderTail
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderPointwise
open OQ14.Maxwell

/-- Coulomb differences away from either singularity have the correct gradient decay. -/
theorem inverse_norm_difference_far (u v : Space)
    (hfar : 2 * ‖u-v‖ ≤ ‖u‖) (hu : u ≠ 0) :
    |‖u‖⁻¹ - ‖v‖⁻¹| ≤ 2 * ‖u-v‖ / ‖u‖^2 := by
  have hdist : |‖u‖ - ‖v‖| ≤ ‖u-v‖ := abs_norm_sub_norm_le u v
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvp : 0 < ‖v‖ := by
    have := (abs_le.mp hdist).2
    linarith
  have hvbound : ‖u‖ ≤ 2 * ‖v‖ := by
    have := (abs_le.mp hdist).2
    linarith
  have heq : |‖u‖⁻¹ - ‖v‖⁻¹| = |‖u‖ - ‖v‖| / (‖u‖ * ‖v‖) := by
    have hi : ‖u‖⁻¹ - ‖v‖⁻¹ = (‖v‖ - ‖u‖) / (‖u‖ * ‖v‖) := by
      field_simp
    rw [hi, abs_div, abs_of_pos (mul_pos hup hvp), abs_sub_comm]
  rw [heq]
  apply (div_le_div_of_nonneg_right hdist (le_of_lt (mul_pos hup hvp))).trans
  apply (div_le_div_iff₀ (mul_pos hup hvp) (sq_pos_of_pos hup)).2
  have hh := mul_nonneg (norm_nonneg (u-v)) (sub_nonneg.mpr hvbound)
  nlinarith

#print axioms OQ14.Packet06GreenHolderPointwise.inverse_norm_difference_far
end OQ14.Packet06GreenHolderPointwise

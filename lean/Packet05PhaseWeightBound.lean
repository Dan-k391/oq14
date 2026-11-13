import Packet05FlatWeight

/-! Both flat dielectric phases have inverse modulus at most one. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhaseWeightBound
open Maxwell Packet05FlatWeight

theorem weight_inverse_bound (d : ℝ) (hd : 0 ≤ d) (x : Space) :
    ‖(weight d x)⁻¹‖ ≤ 1 := by
  have h := FlatDifferenceCoercivity.dielectric_bounds d hd x
  change ‖((FlatDifferenceCoercivity.dielectric d x : ℝ) : ℂ)⁻¹‖ ≤ 1
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < FlatDifferenceCoercivity.dielectric d x)]
  exact (inv_le_one₀ (by linarith : 0 < FlatDifferenceCoercivity.dielectric d x)).2 h.1

end OQ14.Packet05PhaseWeightBound
#print axioms OQ14.Packet05PhaseWeightBound.weight_inverse_bound

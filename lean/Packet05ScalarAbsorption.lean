import Packet05ScalarLocalizedFieldBounds

/-! Quantitative Young absorption for the localized scalar quotient energy. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarAbsorption

theorem three_sum_square_le (x y z : ℝ) : (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x-z), sq_nonneg (y-z)]

theorem absorb_localized_scalar (S X Y K A B D : ℝ)
    (hK : 0 ≤ K)
    (hX : X^2 ≤ 3*S)
    (hpre : S ≤ K*(2*A*X*(B*Y) + D*X + 2*D*(B*Y))) :
    S ≤ 3*K^2*(2*A*B*Y+D)^2 + 2*K*(D^2+(B*Y)^2) := by
  have hsq := sq_nonneg (X - 3*K*(2*A*B*Y+D))
  have hcross := sq_nonneg (D-B*Y)
  have hcrossK := mul_nonneg hK hcross
  nlinarith

end OQ14.Packet05ScalarAbsorption
#print axioms OQ14.Packet05ScalarAbsorption.three_sum_square_le
#print axioms OQ14.Packet05ScalarAbsorption.absorb_localized_scalar

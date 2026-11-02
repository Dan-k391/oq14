import Mathlib

/-!
UNCOMPILED PROPOSAL -- NOT LEAN-VERIFIED IN THIS SESSION.

Packet 03: elementary real algebra for the energy absorption.
Target toolchain: Lean 4.19.0.
Target mathlib: c44e0c8ee63ca166450922a373c7409c5d26b00b.

These lemmas address only the algebra AFTER the analytic energy inequality
has been proved. They do not assert test admissibility, Maxwell regularity,
or the differentiated-curl estimate. No project source is changed.
-/

set_option autoImplicit false

namespace OQ14.Packet03EnergyAlgebra

/-- Young absorption after x is the square root of the weighted energy. -/
theorem half_absorb
    (x y r : ℝ)
    (h : x ^ 2 ≤ r + 2 * x * y) :
    x ^ 2 ≤ 2 * r + 4 * y ^ 2 := by
  nlinarith [sq_nonneg (x - 2 * y)]

/-- A variant retaining a nonnegative coercivity factor explicitly. -/
theorem weighted_half_absorb
    (α x y r : ℝ)
    (hα : 0 ≤ α)
    (h : α * x ^ 2 ≤ r + 2 * x * y) :
    α ^ 2 * x ^ 2 ≤ 2 * α * r + 4 * y ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left h hα
  nlinarith [sq_nonneg (α * x - 2 * y)]

/-- In real coordinates, Re(k^2) is at most |k|^2. -/
theorem complex_mass_real_bound
    (kr ki : ℝ) :
    kr ^ 2 - ki ^ 2 ≤ kr ^ 2 + ki ^ 2 := by
  nlinarith [sq_nonneg ki]

end OQ14.Packet03EnergyAlgebra

#print axioms OQ14.Packet03EnergyAlgebra.half_absorb
#print axioms OQ14.Packet03EnergyAlgebra.weighted_half_absorb
#print axioms OQ14.Packet03EnergyAlgebra.complex_mass_real_bound

/-
Packet 02: elementary complex-vector symmetry algebra.

STATUS: UNCOMPILED PROPOSAL. No Lean compiler was available in the reporting
environment. Intended audit toolchain: Lean 4.19.0 with mathlib commit
c44e0c8ee63ca166450922a373c7409c5d26b00b.

This file is deliberately independent of the OQ14 project. It proves only
finite-dimensional algebraic identities, if it compiles. It does not prove
source covariance, convolution integrability, simultaneous almost-everywhere
covariance, Maxwell regularity, or harmonic reconstruction. The accompanying
report gives the mathematical proofs and the required analytic interfaces.
There are no new axioms or incomplete proof placeholders in this candidate.
-/

import Mathlib

noncomputable section
set_option autoImplicit false

namespace Packet02SymmetryAlgebra

abbrev CVec := Fin 3 → ℂ

/-- Bilinear coordinate pairing. No complex conjugation is inserted. -/
def bilinearDot (u v : CVec) : ℂ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The usual complex-bilinear cross product. -/
def cross (u v : CVec) : CVec :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Rotation about coordinate 2. In applications c = cos θ and s = sin θ. -/
def rotate (c s : ℂ) (v : CVec) : CVec :=
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

/-- Polar reflection in the coordinate-0/coordinate-2 plane. -/
def reflect (v : CVec) : CVec := ![v 0, -v 1, v 2]

/-- Axial-vector reflection: determinant(reflect) times polar reflection. -/
def axialReflect (v : CVec) : CVec := ![-v 0, v 1, -v 2]

theorem axialReflect_eq_neg_reflect (v : CVec) :
    axialReflect v = -reflect v := by
  funext i
  fin_cases i <;> simp [axialReflect, reflect]

theorem cross_rotate (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) (u v : CVec) :
    cross (rotate c s u) (rotate c s v) = rotate c s (cross u v) := by
  funext i
  fin_cases i
  · simp [cross, rotate]
    <;> ring
  · simp [cross, rotate]
    <;> ring
  · change (c * u 0 - s * u 1) * (s * v 0 + c * v 1) -
        (s * u 0 + c * u 1) * (c * v 0 - s * v 1) =
      u 0 * v 1 - u 1 * v 0
    linear_combination (u 0 * v 1 - u 1 * v 0) * hcs

theorem bilinearDot_rotate (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) (u v : CVec) :
    bilinearDot (rotate c s u) (rotate c s v) = bilinearDot u v := by
  change (c * u 0 - s * u 1) * (c * v 0 - s * v 1) +
      (s * u 0 + c * u 1) * (s * v 0 + c * v 1) + u 2 * v 2 =
    u 0 * v 0 + u 1 * v 1 + u 2 * v 2
  linear_combination (u 0 * v 0 + u 1 * v 1) * hcs

theorem complex_trig_relation (θ : ℝ) :
    (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq θ

theorem cross_rotate_angle (θ : ℝ) (u v : CVec) :
    cross (rotate (Real.cos θ) (Real.sin θ) u)
        (rotate (Real.cos θ) (Real.sin θ) v) =
      rotate (Real.cos θ) (Real.sin θ) (cross u v) :=
  cross_rotate _ _ (complex_trig_relation θ) u v

theorem rotate_inverse (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) (v : CVec) :
    rotate c (-s) (rotate c s v) = v := by
  funext i
  fin_cases i
  · change c * (c * v 0 - s * v 1) - (-s) * (s * v 0 + c * v 1) = v 0
    linear_combination v 0 * hcs
  · change (-s) * (c * v 0 - s * v 1) + c * (s * v 0 + c * v 1) = v 1
    linear_combination v 1 * hcs
  · rfl

theorem cross_reflect (u v : CVec) :
    cross (reflect u) (reflect v) = axialReflect (cross u v) := by
  funext i
  fin_cases i <;> simp [cross, reflect, axialReflect] <;> ring

theorem bilinearDot_reflect_axial (x v : CVec) :
    bilinearDot (reflect x) (axialReflect v) = -bilinearDot x v := by
  change x 0 * (-v 0) + (-x 1) * v 1 + x 2 * (-v 2) =
    -(x 0 * v 0 + x 1 * v 1 + x 2 * v 2)
  ring

/-- At a point in the meridional plane, axial reflection forces zero radial dot. -/
theorem meridional_radial_zero (x v : CVec) (hx : x 1 = 0)
    (hv : v = axialReflect v) : bilinearDot x v = 0 := by
  have h0 := congrFun hv (0 : Fin 3)
  have h2 := congrFun hv (2 : Fin 3)
  change v 0 = -v 0 at h0
  change v 2 = -v 2 at h2
  unfold bilinearDot
  rw [hx]
  linear_combination (x 0 / 2) * h0 + (x 2 / 2) * h2

/-- The two stabilizer laws used on the rotation axis force the whole vector to zero. -/
theorem axis_vector_zero (v : CVec) (hrot : rotate (-1) 0 v = v)
    (href : v = axialReflect v) : v = 0 := by
  have h0 := congrFun hrot (0 : Fin 3)
  have h1 := congrFun hrot (1 : Fin 3)
  have h2 := congrFun href (2 : Fin 3)
  change (-1) * v 0 - 0 * v 1 = v 0 at h0
  change 0 * v 0 + (-1) * v 1 = v 1 at h1
  change v 2 = -v 2 at h2
  funext i
  fin_cases i
  · change v 0 = 0
    linear_combination -(1 / 2 : ℂ) * h0
  · change v 1 = 0
    linear_combination -(1 / 2 : ℂ) * h1
  · change v 2 = 0
    linear_combination (1 / 2 : ℂ) * h2

#print axioms Packet02SymmetryAlgebra.cross_rotate
#print axioms Packet02SymmetryAlgebra.bilinearDot_rotate
#print axioms Packet02SymmetryAlgebra.rotate_inverse
#print axioms Packet02SymmetryAlgebra.cross_reflect
#print axioms Packet02SymmetryAlgebra.bilinearDot_reflect_axial
#print axioms Packet02SymmetryAlgebra.meridional_radial_zero
#print axioms Packet02SymmetryAlgebra.axis_vector_zero

end Packet02SymmetryAlgebra

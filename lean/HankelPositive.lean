import HankelPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Positivity and the actual outgoing radial boundary load in every degree. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.HankelPositive

open Polynomial Complex OQ14.ModalAlgebra OQ14.ModalWronskian
  OQ14.HankelPolynomial OQ14.HankelRealBasis OQ14.HankelEnergy
open scoped ComplexConjugate

theorem inversePoly_conj_real (l : ℕ) (w : ℝ) :
    inversePoly l (-I) (w : ℂ) = conj (inversePoly l I (w : ℂ)) := by
  simp [inversePoly, hankelCoeff_conj, map_sum, map_mul, map_pow]

theorem squarePoly_eval_normSq (l : ℕ) (w : ℝ) :
    (squarePoly l).eval (w : ℂ) = (Complex.normSq (inversePoly l I (w : ℂ)) : ℂ) := by
  rw [squarePoly, eval_mul, poly_eval, poly_eval, inversePoly_conj_real, mul_conj]

theorem xi_normSq_polynomial (l : ℕ) (r : ℝ) :
    Complex.normSq (xi l r) = ((squarePoly l).eval ((r⁻¹ : ℝ) : ℂ)).re := by
  rw [squarePoly_eval_normSq, ofReal_re, inversePoly_eq, ofReal_inv, inv_inv,
    xi_normSq_eq]
  rfl

theorem eval_re_nonnegative (p : Polynomial ℂ) (hp : ∀ n, 0 ≤ (p.coeff n).re)
    (w : ℝ) (hw : 0 ≤ w) : 0 ≤ (p.eval (w : ℂ)).re := by
  rw [eval_eq_sum]
  simp only [Polynomial.sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro n _
  simp only [← ofReal_pow, Complex.mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hp n) (pow_nonneg hw n)

theorem squarePoly_derivative_nonnegative (l : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ ((squarePoly l).derivative.eval (w : ℂ)).re := by
  apply eval_re_nonnegative _ _ w hw
  intro n
  rw [coeff_derivative]
  norm_num [Complex.mul_re, Complex.mul_im]
  exact mul_nonneg (squarePoly_coeff_nonnegative l (n+1)) (by positivity)

theorem xi_normSq_hasDerivAt (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => Complex.normSq (xi l x))
      (-((squarePoly l).derivative.eval ((r⁻¹ : ℝ) : ℂ)).re/r^2) r := by
  have h := ((squarePoly l).hasDerivAt (r⁻¹ : ℝ)).real_of_complex.comp r
    ((hasDerivAt_id r).inv hr)
  convert h using 1
  · funext x
    exact xi_normSq_polynomial l x
  · dsimp only [id_eq]
    ring

theorem outgoing_radialLoad_nonpositive (l : ℕ) (r : ℝ) (hr : 0 < r) :
    RadialGreen.radialLoad (xi l r) (xiD l r) ≤ 0 := by
  have hx := (xi_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr.ne')).comp_ofReal
  have he := (RadialGreen.normSq_hasDerivAt hx).unique (xi_normSq_hasDerivAt l r hr.ne')
  have hp := squarePoly_derivative_nonnegative l r⁻¹ (inv_nonneg.mpr hr.le)
  have hd : -((squarePoly l).derivative.eval ((r⁻¹ : ℝ) : ℂ)).re/r^2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp) (sq_nonneg r)
  linarith

end OQ14.HankelPositive

#print axioms OQ14.HankelPositive.inversePoly_conj_real
#print axioms OQ14.HankelPositive.squarePoly_eval_normSq
#print axioms OQ14.HankelPositive.xi_normSq_polynomial
#print axioms OQ14.HankelPositive.eval_re_nonnegative
#print axioms OQ14.HankelPositive.squarePoly_derivative_nonnegative
#print axioms OQ14.HankelPositive.xi_normSq_hasDerivAt
#print axioms OQ14.HankelPositive.outgoing_radialLoad_nonpositive

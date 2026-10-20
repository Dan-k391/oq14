import HankelRealBasis
import Mathlib.Algebra.Polynomial.Derivative

/-! Polynomial identities for the actual finite Hankel series. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.HankelPolynomial

open Polynomial Complex OQ14.ModalAlgebra OQ14.ModalWronskian

def poly (l : ℕ) (phase : ℂ) : Polynomial ℂ :=
  ∑ s ∈ Finset.range (l+1), C (hankelCoeff l s phase) * X^s

theorem poly_eval (l : ℕ) (phase w : ℂ) :
    (poly l phase).eval w = inversePoly l phase w := by
  simp [poly, inversePoly, eval_finset_sum, eval_mul, eval_pow]

theorem poly_coeff (l n : ℕ) (phase : ℂ) :
    (poly l phase).coeff n = if n ≤ l then hankelCoeff l n phase else 0 := by
  simp [poly, finset_sum_coeff, coeff_C_mul_X_pow, Nat.lt_succ_iff]

theorem euler_coeff (p : Polynomial ℂ) (n : ℕ) :
    (X*p.derivative).coeff n = (n : ℂ)*p.coeff n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_derivative, mul_comm]

theorem poly_coeff_relation (l n : ℕ) (phase : ℂ) (hp : phase^2 = -1) :
    2*phase*(n+1 : ℕ)*(poly l phase).coeff (n+1) =
      ((n : ℂ)*(n+1)-(l : ℂ)*(l+1))*(poly l phase).coeff n := by
  by_cases hn : n < l
  · rw [poly_coeff, poly_coeff, if_pos (by omega), if_pos (by omega)]
    exact hankelCoeff_ode_relation l n phase hp hn
  · by_cases he : n = l
    · subst n
      simp [poly_coeff]
    · have hnl : ¬ n ≤ l := by omega
      have hnsl : ¬ n+1 ≤ l := by omega
      simp [poly_coeff, hnl, hnsl]

theorem poly_ode (l : ℕ) (phase : ℂ) (hp : phase^2 = -1) :
    X^2*(poly l phase).derivative.derivative +
      2*X*(poly l phase).derivative - C (2*phase)*(poly l phase).derivative -
      C ((l : ℂ)*(l+1))*poly l phase = 0 := by
  have he : X*(X*(poly l phase).derivative).derivative +
      X*(poly l phase).derivative - C (2*phase)*(poly l phase).derivative -
      C ((l : ℂ)*(l+1))*poly l phase = 0 := by
    ext n
    simp only [coeff_sub, coeff_add, euler_coeff, coeff_C_mul, coeff_derivative, coeff_zero]
    have h := poly_coeff_relation l n phase hp
    push_cast at h
    linear_combination -h
  simp only [derivative_mul, derivative_X, one_mul] at he
  linear_combination he

def squarePoly (l : ℕ) : Polynomial ℂ := poly l I * poly l (-I)

theorem product_ode (u v : Polynomial ℂ) (ν : ℂ)
    (hu : X^2*u.derivative.derivative + 2*X*u.derivative -
      C (2*I)*u.derivative - C ν*u = 0)
    (hv : X^2*v.derivative.derivative + 2*X*v.derivative -
      C (2*(-I))*v.derivative - C ν*v = 0) :
    X^4*(u*v).derivative.derivative.derivative +
      6*X^3*(u*v).derivative.derivative +
      C (6-4*ν)*X^2*(u*v).derivative + 4*(u*v).derivative -
      C (4*ν)*X*(u*v) = 0 := by
  have hu' := congrArg Polynomial.derivative hu
  have hv' := congrArg Polynomial.derivative hv
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, derivative_zero,
    zero_mul, mul_zero, zero_add, add_zero, mul_one, one_mul,
    Nat.cast_ofNat, Nat.reduceSub, pow_one] at hu' hv'
  simp only [map_mul, map_neg, map_ofNat, map_sub] at hu hv hu' hv' ⊢
  simp only [derivative_mul, derivative_add]
  have hi : (C I : Polynomial ℂ)^2 = -1 := by rw [← map_pow, I_sq]; simp
  linear_combination X^2*(v*hu' + u*hv') +
    3*X^2*(v.derivative*hu + u.derivative*hv) +
    2*(X+C I)*v*hu + 2*(X-C I)*u*hv +
    4*(u.derivative*v+u*v.derivative)*hi

theorem squarePoly_ode (l : ℕ) :
    X^4*(squarePoly l).derivative.derivative.derivative +
      6*X^3*(squarePoly l).derivative.derivative +
      C (6-4*((l : ℂ)*(l+1)))*X^2*(squarePoly l).derivative +
      4*(squarePoly l).derivative - C (4*((l : ℂ)*(l+1)))*X*squarePoly l = 0 :=
  product_ode _ _ _ (poly_ode l I (by norm_num)) (poly_ode l (-I) (by norm_num))

def euler (p : Polynomial ℂ) : Polynomial ℂ := X*p.derivative

theorem squarePoly_euler_ode (l : ℕ) :
    X*(euler (euler (euler (squarePoly l))) + 3*euler (euler (squarePoly l)) +
      C (2-4*((l : ℂ)*(l+1)))*euler (squarePoly l) -
      C (4*((l : ℂ)*(l+1)))*squarePoly l) + 4*(squarePoly l).derivative = 0 := by
  have h := squarePoly_ode l
  simp only [euler, derivative_mul, derivative_add, derivative_X, one_mul,
    derivative_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  simp only [map_sub, map_mul, map_ofNat] at h ⊢
  linear_combination h

theorem squarePoly_coeff_zero (l : ℕ) : (squarePoly l).coeff 0 = 1 := by
  simp [squarePoly, mul_coeff_zero, poly_coeff, hankelCoeff, factorial_cast_ne_zero]
  field_simp [factorial_cast_ne_zero]

theorem squarePoly_coeff_one (l : ℕ) : (squarePoly l).coeff 1 = 0 := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff 0) (squarePoly_euler_ode l)
  simp [coeff_derivative] at h
  exact h

theorem squarePoly_coeff_recurrence (l n : ℕ) :
    4*(n+2 : ℂ)*(squarePoly l).coeff (n+2) =
      (n+1 : ℂ)*(4*((l : ℂ)*(l+1))-(n : ℂ)*(n+2))*(squarePoly l).coeff n := by
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (n+1)) (squarePoly_euler_ode l)
  simp only [coeff_add, coeff_sub, coeff_X_mul, coeff_ofNat_mul, coeff_C_mul,
    euler, euler_coeff, coeff_derivative, coeff_zero] at h
  push_cast at h
  linear_combination h

theorem poly_degree (l : ℕ) (phase : ℂ) : (poly l phase).natDegree ≤ l := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [poly_coeff, not_le.mpr hn]

theorem squarePoly_degree (l : ℕ) : (squarePoly l).natDegree ≤ 2*l := by
  exact (natDegree_mul_le.trans (add_le_add (poly_degree l I) (poly_degree l (-I)))).trans_eq (by omega)

theorem squarePoly_coeff_nonnegative (l n : ℕ) : 0 ≤ ((squarePoly l).coeff n).re := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : 2*l < n
    · rw [coeff_eq_zero_of_natDegree_lt ((squarePoly_degree l).trans_lt hn)]
      simp
    · cases n with
      | zero => simp [squarePoly_coeff_zero]
      | succ n =>
        cases n with
        | zero => simp [squarePoly_coeff_one]
        | succ n =>
          have hprev : 0 ≤ ((squarePoly l).coeff n).re := ih n (by omega)
          have hnl : (n : ℝ) ≤ 2*l := by exact_mod_cast (by omega : n ≤ 2*l)
          have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hll : (0 : ℝ) ≤ l := Nat.cast_nonneg l
          have hfactor : 0 ≤ (4 : ℝ)*((l : ℝ)*(l+1))-(n : ℝ)*(n+2) := by
            nlinarith [mul_nonneg (by linarith : 0 ≤ 2*(l : ℝ)-(n : ℝ))
              (by positivity : 0 ≤ 2*(l : ℝ)+(n : ℝ)+2)]
          have h := congrArg Complex.re (squarePoly_coeff_recurrence l n)
          norm_num [Complex.mul_re, Complex.mul_im] at h
          have hp : 0 ≤ (n+1 : ℝ)*(4*((l : ℝ)*(l+1))-(n : ℝ)*(n+2))*
              ((squarePoly l).coeff n).re := mul_nonneg (mul_nonneg (by positivity) hfactor) hprev
          have hc : (0 : ℝ) < 4*(n+2 : ℝ) := by positivity
          change 0 ≤ ((squarePoly l).coeff (n+2)).re
          nlinarith

end OQ14.HankelPolynomial

#print axioms OQ14.HankelPolynomial.poly_eval
#print axioms OQ14.HankelPolynomial.poly_coeff
#print axioms OQ14.HankelPolynomial.euler_coeff
#print axioms OQ14.HankelPolynomial.poly_coeff_relation
#print axioms OQ14.HankelPolynomial.poly_ode
#print axioms OQ14.HankelPolynomial.product_ode
#print axioms OQ14.HankelPolynomial.squarePoly_ode
#print axioms OQ14.HankelPolynomial.squarePoly_euler_ode
#print axioms OQ14.HankelPolynomial.squarePoly_coeff_zero
#print axioms OQ14.HankelPolynomial.squarePoly_coeff_one
#print axioms OQ14.HankelPolynomial.squarePoly_coeff_recurrence
#print axioms OQ14.HankelPolynomial.poly_degree
#print axioms OQ14.HankelPolynomial.squarePoly_degree
#print axioms OQ14.HankelPolynomial.squarePoly_coeff_nonnegative

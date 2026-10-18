import ModalWronskian
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
# Finite polynomial obstruction to multiple spherical TM poles

The matching Laurent functions are represented by actual finite polynomials
in the inverse coordinate. Hypothetical multiple poles and common poles of
distinct degrees are roots of explicit nonzero polynomials. Nonvanishing of
the latter polynomial follows from the first two actual series coefficients.
This gives finite exceptional sets without assuming any transcendence
theorem. It does not assert that these sets are empty or that their countable
union misses a pole, and does not identify Maxwell operator multiplicities.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalRational

open Complex Polynomial OQ14.ModalAlgebra OQ14.ModalWronskian

def inversePolynomial (l : ℕ) (phase : ℂ) : Polynomial ℂ :=
  ∑ s ∈ Finset.range (l + 1), C (hankelCoeff l s phase) * X ^ s

theorem inversePolynomial_eval (l : ℕ) (phase w : ℂ) :
    (inversePolynomial l phase).eval w = inversePoly l phase w := by
  simp [inversePolynomial, inversePoly, eval_finset_sum]

theorem inversePolynomial_derivative_eval (l : ℕ) (phase w : ℂ) :
    (inversePolynomial l phase).derivative.eval w = inversePolyD l phase w := by
  have h := (inversePolynomial l phase).hasDerivAt w
  have heq : (fun x => (inversePolynomial l phase).eval x) = inversePoly l phase :=
    funext (inversePolynomial_eval l phase)
  rw [heq] at h
  exact h.unique (inversePoly_hasDerivAt l phase w)

def plusPolynomial (l : ℕ) (n : ℂ) : Polynomial ℂ :=
  C ((-I) ^ (l + 1)) *
    (C (I * (n - 1)) * inversePolynomial l I *
        (inversePolynomial l I).comp (C n⁻¹ * X) -
      C n * X ^ 2 * (inversePolynomial l I).comp (C n⁻¹ * X) *
        (inversePolynomial l I).derivative +
      (C n⁻¹ * X) ^ 2 * inversePolynomial l I *
        (inversePolynomial l I).derivative.comp (C n⁻¹ * X))

def minusPolynomial (l : ℕ) (n : ℂ) : Polynomial ℂ :=
  C (I ^ (l + 1)) *
    (C (I * (n + 1)) * inversePolynomial l I *
        (inversePolynomial l (-I)).comp (C n⁻¹ * X) -
      C n * X ^ 2 * (inversePolynomial l (-I)).comp (C n⁻¹ * X) *
        (inversePolynomial l I).derivative +
      (C n⁻¹ * X) ^ 2 * inversePolynomial l I *
        (inversePolynomial l (-I)).derivative.comp (C n⁻¹ * X))

theorem plusPolynomial_eval (l : ℕ) (n w : ℂ) (hn : n ≠ 0) (hw : w ≠ 0) :
    (plusPolynomial l n).eval w = cPlus l n w⁻¹ := by
  have harg : n * w⁻¹ = (n⁻¹ * w)⁻¹ := by field_simp
  have harg0 : n⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hn) hw
  unfold plusPolynomial cPlus p pD
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_X, eval_comp,
    inversePolynomial_eval, inversePolynomial_derivative_eval]
  rw [harg, inversePolyD_eq l I w hw, inversePolyD_eq l I (n⁻¹ * w) harg0,
    ← inversePoly_eq l I w, ← inversePoly_eq l I (n⁻¹ * w)]
  ring

theorem minusPolynomial_eval (l : ℕ) (n w : ℂ) (hn : n ≠ 0) (hw : w ≠ 0) :
    (minusPolynomial l n).eval w = cMinus l n w⁻¹ := by
  have harg : n * w⁻¹ = (n⁻¹ * w)⁻¹ := by field_simp
  have harg0 : n⁻¹ * w ≠ 0 := mul_ne_zero (inv_ne_zero hn) hw
  unfold minusPolynomial cMinus p pD pMinus pMinusD
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_X, eval_comp,
    inversePolynomial_eval, inversePolynomial_derivative_eval]
  rw [harg, inversePolyD_eq l I w hw, inversePolyD_eq l (-I) (n⁻¹ * w) harg0,
    ← inversePoly_eq l I w, ← inversePoly_eq l (-I) (n⁻¹ * w)]
  ring

theorem plusPolynomial_zero (l : ℕ) (n : ℂ) :
    (plusPolynomial l n).eval 0 = (-I) ^ (l + 1) * I * (n - 1) := by
  simp [plusPolynomial, inversePolynomial_eval, inversePoly_zero]
  ring

theorem minusPolynomial_zero (l : ℕ) (n : ℂ) :
    (minusPolynomial l n).eval 0 = I ^ (l + 1) * I * (n + 1) := by
  simp [minusPolynomial, inversePolynomial_eval, inversePoly_zero]
  ring

def multiplicityPolynomial (l : ℕ) (n : ℂ) : Polynomial ℂ :=
  X ^ 2 * ((minusPolynomial l n).derivative * plusPolynomial l n -
    minusPolynomial l n * (plusPolynomial l n).derivative) +
    C (2 * I * n) * minusPolynomial l n * plusPolynomial l n

theorem multiplicityPolynomial_zero (l : ℕ) (n : ℂ) :
    (multiplicityPolynomial l n).eval 0 =
      2 * I * n * (I ^ (l + 1) * I * (n + 1)) *
        ((-I) ^ (l + 1) * I * (n - 1)) := by
  simp [multiplicityPolynomial, plusPolynomial_zero, minusPolynomial_zero]

theorem multiplicityPolynomial_ne_zero (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) :
    multiplicityPolynomial l n ≠ 0 := by
  have hap : (-I) ^ (l + 1) * I * (n - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) I_ne_zero)
      (sub_ne_zero.mpr hp)
  have han : n + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hm
  have ham : I ^ (l + 1) * I * (n + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) I_ne_zero) han
  intro hzero
  have h := congrArg (fun p : Polynomial ℂ => p.eval 0) hzero
  dsimp only at h
  rw [multiplicityPolynomial_zero] at h
  have he : 2 * I * n * (I ^ (l + 1) * I * (n + 1)) *
      ((-I) ^ (l + 1) * I * (n - 1)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn) ham) hap
  exact he (by simpa only [eval_zero] using h)

theorem rationalPole_inverse (l : ℕ) (n w : ℂ) (hn : n ≠ 0) (hw : w ≠ 0) :
    rationalPole l n w⁻¹ =
      -(minusPolynomial l n).eval w / (plusPolynomial l n).eval w := by
  rw [plusPolynomial_eval l n w hn hw, minusPolynomial_eval l n w hn hw]
  rfl

/-- A hypothetical multiple determinant zero is a root of the explicit
inverse-coordinate multiplicity polynomial. -/
theorem multiple_zero_is_polynomial_root (l : ℕ) (n z : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) (hd : tmDet l n z = 0)
    (hdd : deriv (tmDet l n) z = 0) :
    (multiplicityPolynomial l n).eval z⁻¹ = 0 := by
  have hcp := plus_ne_zero_at_pole l n z hn hz hd
  have hc := coefficients_differentiableAt l n z hn hz
  have hr : DifferentiableAt ℂ (rationalPole l n) z := hc.2.neg.div hc.1 hcp
  have hrd := hr.hasDerivAt
  rw [(multiple_zero_rational_condition l n z hn hz hd hdd).2] at hrd
  have hrdi : HasDerivAt (rationalPole l n)
      (2 * I * n * rationalPole l n z) (z⁻¹)⁻¹ := by simpa using hrd
  have hchain := hrdi.comp z⁻¹ ((hasDerivAt_id z⁻¹).inv (inv_ne_zero hz))
  simp only [inv_inv, id_eq] at hchain
  have hpa : (plusPolynomial l n).eval z⁻¹ ≠ 0 := by
    rw [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv]
    exact hcp
  have hquot := ((minusPolynomial l n).hasDerivAt z⁻¹).neg.div
    ((plusPolynomial l n).hasDerivAt z⁻¹) hpa
  have hcongr : HasDerivAt
      (fun w : ℂ => -(minusPolynomial l n).eval w / (plusPolynomial l n).eval w)
      ((2 * I * n * rationalPole l n z) * (-1 / (z⁻¹) ^ 2)) z⁻¹ := by
    apply hchain.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (inv_ne_zero hz)] with w hw
    exact (rationalPole_inverse l n w hn hw).symm
  have he := hquot.unique hcongr
  have hre : rationalPole l n z =
      -(minusPolynomial l n).eval z⁻¹ / (plusPolynomial l n).eval z⁻¹ := by
    simpa using rationalPole_inverse l n z⁻¹ hn (inv_ne_zero hz)
  rw [hre] at he
  have hpa' : (plusPolynomial l n).eval (1 / z) ≠ 0 := by
    simpa only [one_div] using hpa
  field_simp [hpa, hpa', hz] at he
  have he' : -(minusPolynomial l n).derivative.eval (1 / z) *
      (plusPolynomial l n).eval (1 / z) +
      (minusPolynomial l n).eval (1 / z) * (plusPolynomial l n).derivative.eval (1 / z) =
      2 * I * n * (minusPolynomial l n).eval (1 / z) * z ^ 2 *
        (plusPolynomial l n).eval (1 / z) := by
    apply mul_right_cancel₀ hpa'
    linear_combination he
  unfold multiplicityPolynomial
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_sub]
  field_simp [hz]
  linear_combination -he'

/-- For a fixed degree and fixed n outside 0,+1,-1, only finitely many
nonzero determinant zeros can be multiple. This does not assert that the
finite exceptional set is empty. -/
theorem finite_multiple_zeros (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) :
    Set.Finite {z : ℂ | z ≠ 0 ∧ tmDet l n z = 0 ∧ deriv (tmDet l n) z = 0} := by
  have hf := finite_setOf_isRoot (multiplicityPolynomial_ne_zero l n hn hp hm)
  apply (hf.image (fun w : ℂ => w⁻¹)).subset
  intro z hz
  refine ⟨z⁻¹, ?_, inv_inv z⟩
  exact multiple_zero_is_polynomial_root l n z hn hz.1 hz.2.1 hz.2.2

theorem inversePolyD_zero (l : ℕ) (phase : ℂ) :
    inversePolyD l phase 0 = phase * (l : ℂ) * (l + 1) / 2 := by
  rcases l with _ | l
  · simp [inversePolyD]
  have hval : inversePolyD (l + 1) phase 0 = hankelCoeff (l + 1) 1 phase := by
    unfold inversePolyD
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp
  rw [hval]
  have hr := hankelCoeff_recurrence (l + 1) 0 phase (Nat.succ_pos l)
  have hc : hankelCoeff (l + 1) 0 phase = 1 := by
    simp [hankelCoeff]
    exact div_self (factorial_cast_ne_zero (l + 1))
  simp only [Nat.zero_add, Nat.sub_zero, Nat.cast_one, mul_one, hc] at hr
  push_cast at hr ⊢
  linear_combination (1 / 2 : ℂ) * hr

theorem plusPolynomial_derivative_zero (l : ℕ) (n : ℂ) :
    (plusPolynomial l n).derivative.eval 0 =
      (-I) ^ (l + 1) * I * (n - 1) *
        (I * (l : ℂ) * (l + 1) / 2 * (1 + n⁻¹)) := by
  simp only [plusPolynomial, derivative_mul, derivative_add, derivative_sub,
    derivative_C, derivative_pow, derivative_X, derivative_comp,
    eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_zero, eval_one,
    inversePolynomial_eval, inversePolynomial_derivative_eval]
  simp only [mul_zero, zero_mul, zero_add, add_zero, pow_one, zero_pow (by decide : 2 ≠ 0),
    inversePoly_zero, inversePolyD_zero, mul_one, one_mul, zero_sub]
  ring

theorem minusPolynomial_derivative_zero (l : ℕ) (n : ℂ) :
    (minusPolynomial l n).derivative.eval 0 =
      I ^ (l + 1) * I * (n + 1) *
        (I * (l : ℂ) * (l + 1) / 2 * (1 - n⁻¹)) := by
  simp only [minusPolynomial, derivative_mul, derivative_add, derivative_sub,
    derivative_C, derivative_pow, derivative_X, derivative_comp,
    eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_comp, eval_zero, eval_one,
    inversePolynomial_eval, inversePolynomial_derivative_eval]
  simp only [mul_zero, zero_mul, zero_add, add_zero, pow_one, zero_pow (by decide : 2 ≠ 0),
    inversePoly_zero, inversePolyD_zero, mul_one, one_mul, zero_sub]
  ring

def separationPolynomial (l j : ℕ) (n : ℂ) : Polynomial ℂ :=
  plusPolynomial l n * minusPolynomial j n -
    plusPolynomial j n * minusPolynomial l n

/-- The first two inverse-coordinate coefficients distinguish every pair
of degrees. This does not require a parity split or transcendence. -/
theorem separationPolynomial_ne_zero (l j : ℕ) (n : ℂ)
    (hlj : l ≠ j) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) :
    separationPolynomial l j n ≠ 0 := by
  let a : ℂ := (-I) ^ (l + 1) * I * (n - 1)
  let b : ℂ := I ^ (l + 1) * I * (n + 1)
  let c : ℂ := (-I) ^ (j + 1) * I * (n - 1)
  let d : ℂ := I ^ (j + 1) * I * (n + 1)
  let u : ℂ := (l : ℂ) * (l + 1)
  let v : ℂ := (j : ℂ) * (j + 1)
  intro hzero
  have he := congrArg (fun p : Polynomial ℂ => p.eval 0) hzero
  have hd := congrArg (fun p : Polynomial ℂ => p.derivative.eval 0) hzero
  have heq : a * d - c * b = 0 := by
    simpa only [separationPolynomial, eval_sub, eval_mul, plusPolynomial_zero,
      minusPolynomial_zero, eval_zero] using he
  have hdeq : a * (I * u / 2 * (1 + n⁻¹)) * d +
      a * (d * (I * v / 2 * (1 - n⁻¹))) -
      (c * (I * v / 2 * (1 + n⁻¹)) * b +
        c * (b * (I * u / 2 * (1 - n⁻¹)))) = 0 := by
    simpa only [separationPolynomial, derivative_sub, derivative_mul,
      derivative_zero, eval_add, eval_sub, eval_mul, eval_zero,
      plusPolynomial_zero, minusPolynomial_zero,
      plusPolynomial_derivative_zero, minusPolynomial_derivative_zero,
      a, b, c, d, u, v, mul_assoc] using hd
  have hfactor : (a * d * I * n⁻¹) * (u - v) = 0 := by
    linear_combination hdeq -
      (I * v / 2 * (1 + n⁻¹) + I * u / 2 * (1 - n⁻¹)) * heq
  have ha : a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) I_ne_zero)
      (sub_ne_zero.mpr hp)
  have hnp : n + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hm
  have hd0 : d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) I_ne_zero) hnp
  have huv : u - v = 0 := (mul_eq_zero.mp hfactor).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hd0) I_ne_zero) (inv_ne_zero hn))
  have hcEq : (l : ℂ) * (l + 1) = (j : ℂ) * (j + 1) := sub_eq_zero.mp huv
  have hnEq : l * (l + 1) = j * (j + 1) := by exact_mod_cast hcEq
  apply hlj
  nlinarith

theorem common_zero_is_polynomial_root (l j : ℕ) (n z : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) (hl : tmDet l n z = 0) (hj : tmDet j n z = 0) :
    (separationPolynomial l j n).eval z⁻¹ = 0 := by
  have hlp := plus_ne_zero_at_pole l n z hn hz hl
  have hjp := plus_ne_zero_at_pole j n z hn hz hj
  have hratio : rationalPole l n z = rationalPole j n z :=
    ((tmDet_zero_iff_exp l n z hlp).mp hl).symm.trans
      ((tmDet_zero_iff_exp j n z hjp).mp hj)
  have hal : (plusPolynomial l n).eval z⁻¹ ≠ 0 := by
    simpa only [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv] using hlp
  have haj : (plusPolynomial j n).eval z⁻¹ ≠ 0 := by
    simpa only [plusPolynomial_eval j n z⁻¹ hn (inv_ne_zero hz), inv_inv] using hjp
  have hrl : rationalPole l n z =
      -(minusPolynomial l n).eval z⁻¹ / (plusPolynomial l n).eval z⁻¹ := by
    simpa using rationalPole_inverse l n z⁻¹ hn (inv_ne_zero hz)
  have hrj : rationalPole j n z =
      -(minusPolynomial j n).eval z⁻¹ / (plusPolynomial j n).eval z⁻¹ := by
    simpa using rationalPole_inverse j n z⁻¹ hn (inv_ne_zero hz)
  rw [hrl, hrj] at hratio
  have hcross := (div_eq_div_iff hal haj).mp hratio
  simp only [separationPolynomial, eval_sub, eval_mul]
  linear_combination hcross

theorem finite_common_zeros (l j : ℕ) (n : ℂ)
    (hlj : l ≠ j) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) :
    Set.Finite {z : ℂ | z ≠ 0 ∧ tmDet l n z = 0 ∧ tmDet j n z = 0} := by
  have hf := finite_setOf_isRoot (separationPolynomial_ne_zero l j n hlj hn hp hm)
  apply (hf.image (fun w : ℂ => w⁻¹)).subset
  intro z hz
  refine ⟨z⁻¹, ?_, inv_inv z⟩
  exact common_zero_is_polynomial_root l j n z hn hz.1 hz.2.1 hz.2.2

end OQ14.ModalRational

#print axioms OQ14.ModalRational.inversePolynomial_eval
#print axioms OQ14.ModalRational.inversePolynomial_derivative_eval
#print axioms OQ14.ModalRational.plusPolynomial_eval
#print axioms OQ14.ModalRational.minusPolynomial_eval
#print axioms OQ14.ModalRational.plusPolynomial_zero
#print axioms OQ14.ModalRational.minusPolynomial_zero
#print axioms OQ14.ModalRational.multiplicityPolynomial_zero
#print axioms OQ14.ModalRational.multiplicityPolynomial_ne_zero
#print axioms OQ14.ModalRational.rationalPole_inverse
#print axioms OQ14.ModalRational.multiple_zero_is_polynomial_root
#print axioms OQ14.ModalRational.finite_multiple_zeros
#print axioms OQ14.ModalRational.inversePolyD_zero
#print axioms OQ14.ModalRational.plusPolynomial_derivative_zero
#print axioms OQ14.ModalRational.minusPolynomial_derivative_zero
#print axioms OQ14.ModalRational.separationPolynomial_ne_zero
#print axioms OQ14.ModalRational.common_zero_is_polynomial_root
#print axioms OQ14.ModalRational.finite_common_zeros

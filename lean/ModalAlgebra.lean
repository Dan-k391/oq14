import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FunProp

/-!
# Explicit spherical-pole determinant algebra

The finite Riccati--Hankel polynomials and their derivatives are defined
explicitly. The TM determinant factorization is proved by algebra from
these functions, with actual complex derivatives certified away from zero.
This file does not assume pole simplicity or separation. Transcendence,
identification with the Maxwell Fredholm multiplicity, and the general
Hankel Wronskian are not claimed to be formalized here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.ModalAlgebra

open Complex

def hankelCoeff (l s : ℕ) (phase : ℂ) : ℂ :=
  phase ^ s * (Nat.factorial (l + s) : ℂ) /
    (2 ^ s * (Nat.factorial s : ℂ) * (Nat.factorial (l - s) : ℂ))

def hankelPoly (l : ℕ) (phase z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l + 1), hankelCoeff l s phase * z ^ (-(s : ℤ))

def hankelPolyD (l : ℕ) (phase z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l + 1),
    hankelCoeff l s phase * ((-(s : ℤ) : ℂ) * z ^ (-(s : ℤ) - 1))

def hankelPolyDD (l : ℕ) (phase z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l + 1),
    hankelCoeff l s phase * ((-(s : ℤ) : ℂ) *
      (((-(s : ℤ) - 1 : ℤ) : ℂ) * z ^ (-(s : ℤ) - 1 - 1)))

theorem hankelPoly_hasDerivAt (l : ℕ) (phase z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (hankelPoly l phase) (hankelPolyD l phase z) z := by
  apply HasDerivAt.sum
  intro s _
  simpa using (hasDerivAt_zpow (-(s : ℤ)) z (Or.inl hz)).const_mul
    (hankelCoeff l s phase)

theorem hankelPolyD_hasDerivAt (l : ℕ) (phase z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (hankelPolyD l phase) (hankelPolyDD l phase z) z := by
  apply HasDerivAt.sum
  intro s _
  simpa using
    ((hasDerivAt_zpow (-(s : ℤ) - 1) z (Or.inl hz)).const_mul
      (-(s : ℤ) : ℂ)).const_mul (hankelCoeff l s phase)

def p (l : ℕ) (z : ℂ) : ℂ := hankelPoly l I z
def pD (l : ℕ) (z : ℂ) : ℂ := hankelPolyD l I z
def pMinus (l : ℕ) (z : ℂ) : ℂ := hankelPoly l (-I) z
def pMinusD (l : ℕ) (z : ℂ) : ℂ := hankelPolyD l (-I) z

def xi (l : ℕ) (z : ℂ) : ℂ := (-I) ^ (l + 1) * exp (I * z) * p l z
def xiD (l : ℕ) (z : ℂ) : ℂ :=
  (-I) ^ (l + 1) * exp (I * z) * (I * p l z + pD l z)
def xiMinus (l : ℕ) (z : ℂ) : ℂ :=
  I ^ (l + 1) * exp (-I * z) * pMinus l z
def xiMinusD (l : ℕ) (z : ℂ) : ℂ :=
  I ^ (l + 1) * exp (-I * z) * (-I * pMinus l z + pMinusD l z)

theorem xi_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (xi l) (xiD l z) z := by
  have he : HasDerivAt (fun w : ℂ => exp (I * w)) (exp (I * z) * I) z :=
    by simpa using ((hasDerivAt_id z).const_mul I).cexp
  have hp := hankelPoly_hasDerivAt l I z hz
  convert (he.const_mul ((-I) ^ (l + 1))).mul hp using 1 <;>
    simp only [xi, xiD, p, pD] <;> ring

theorem xiMinus_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (xiMinus l) (xiMinusD l z) z := by
  have he : HasDerivAt (fun w : ℂ => exp (-I * w)) (exp (-I * z) * (-I)) z :=
    by simpa using ((hasDerivAt_id z).const_mul (-I)).cexp
  have hp := hankelPoly_hasDerivAt l (-I) z hz
  convert (he.const_mul (I ^ (l + 1))).mul hp using 1 <;>
    simp only [xiMinus, xiMinusD, pMinus, pMinusD] <;> ring

def psi (l : ℕ) (z : ℂ) : ℂ := (xi l z + xiMinus l z) / 2
def psiD (l : ℕ) (z : ℂ) : ℂ := (xiD l z + xiMinusD l z) / 2

theorem psi_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (psi l) (psiD l z) z := by
  exact ((xi_hasDerivAt l z hz).add (xiMinus_hasDerivAt l z hz)).div_const 2

def tmDet (l : ℕ) (n z : ℂ) : ℂ :=
  n * psi l (n * z) * xiD l z - xi l z * psiD l (n * z)

def cPlus (l : ℕ) (n z : ℂ) : ℂ :=
  (-I) ^ (l + 1) *
    (I * (n - 1) * p l z * p l (n * z) +
      n * p l (n * z) * pD l z - p l z * pD l (n * z))

def cMinus (l : ℕ) (n z : ℂ) : ℂ :=
  I ^ (l + 1) *
    (I * (n + 1) * p l z * pMinus l (n * z) +
      n * pMinus l (n * z) * pD l z - p l z * pMinusD l (n * z))

/-- The exact determinant identity, including its nonzero exponential factor. -/
theorem tmDet_exp_factorization (l : ℕ) (n z : ℂ) :
    tmDet l n z = ((-I) ^ (l + 1) * exp (I * z) / 2) *
      (cPlus l n z * exp (I * (n * z)) +
       cMinus l n z * exp (-I * (n * z))) := by
  unfold tmDet psi psiD xi xiD xiMinus xiMinusD cPlus cMinus
  ring

theorem determinant_prefactor_ne_zero (l : ℕ) (z : ℂ) :
    (-I) ^ (l + 1) * exp (I * z) / 2 ≠ 0 := by
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero))
    (exp_ne_zero _)) (by norm_num)

def rationalPole (l : ℕ) (n z : ℂ) : ℂ := -cMinus l n z / cPlus l n z

theorem exp_double_split (w : ℂ) :
    exp w = exp (-w) * exp (2 * w) := by
  rw [← exp_add]
  congr 1
  ring

/-- At a nonvanishing plus coefficient the pole equation is exactly rational. -/
theorem tmDet_zero_iff_exp (l : ℕ) (n z : ℂ) (hc : cPlus l n z ≠ 0) :
    tmDet l n z = 0 ↔ exp (2 * I * n * z) = rationalPole l n z := by
  rw [tmDet_exp_factorization, mul_eq_zero]
  simp only [determinant_prefactor_ne_zero, false_or]
  have he := exp_ne_zero (-I * (n * z))
  have hs : exp (I * (n * z)) =
      exp (-I * (n * z)) * exp (2 * I * n * z) := by
    convert exp_double_split (I * (n * z)) using 1 <;> congr 1 <;> ring
  rw [hs]
  unfold rationalPole
  constructor
  · intro h
    apply (eq_div_iff hc).2
    have h' : exp (-I * (n * z)) *
        (exp (2 * I * n * z) * cPlus l n z + cMinus l n z) = 0 := by
      linear_combination h
    have h'' := (mul_eq_zero.mp h').resolve_left he
    linear_combination h''
  · intro h
    have h' := (eq_div_iff hc).1 h
    linear_combination exp (-I * (n * z)) * h'

/-- A zero with nonzero plus coefficient also has nonzero minus coefficient. -/
theorem minus_ne_zero_at_pole (l : ℕ) (n z : ℂ)
    (hc : cPlus l n z ≠ 0) (hd : tmDet l n z = 0) : cMinus l n z ≠ 0 := by
  intro hm
  have h := (tmDet_zero_iff_exp l n z hc).1 hd
  simpa [rationalPole, hm] using h

/-- A nonzero interior Wronskian precludes simultaneous annihilation of
both independent interior solutions by nonzero exterior matching data. -/
theorem matching_pair_not_both_zero
    (n u v du dv x dx : ℂ) (hn : n ≠ 0)
    (hw : u * dv - v * du ≠ 0) (hx : x ≠ 0 ∨ dx ≠ 0) :
    ¬(n * u * dx - x * du = 0 ∧ n * v * dx - x * dv = 0) := by
  rintro ⟨h₁, h₂⟩
  have he : x * (u * dv - v * du) = 0 := by
    linear_combination v * h₁ - u * h₂
  have hx0 : x = 0 := (mul_eq_zero.mp he).resolve_right hw
  have hd : n * dx * (u * dv - v * du) = 0 := by
    linear_combination dv * h₁ - du * h₂
  have hdx0 : dx = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right hw)).resolve_left hn
  exact hx.elim (fun h => h hx0) (fun h => h hdx0)

/-- The differential algebra used at a hypothetical multiple pole.
The hypotheses are the explicit zero equations for the exponential sum
and its derivative, not a simplicity or rational-derivative conclusion. -/
theorem quotient_derivative_of_double_exp_zero
    (f g : ℂ → ℂ) (f' g' a z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z)
    (hf0 : f z ≠ 0)
    (hzero : f z * exp (a * z) + g z * exp (-a * z) = 0)
    (hderiv : (f' + a * f z) * exp (a * z) +
      (g' - a * g z) * exp (-a * z) = 0) :
    HasDerivAt (fun w => -g w / f w) (2 * a * (-g z / f z)) z := by
  have hprod : (g z * f' - g' * f z + 2 * a * g z * f z) *
      exp (-a * z) = 0 := by
    linear_combination (f' + a * f z) * hzero - f z * hderiv
  have hnum := (mul_eq_zero.mp hprod).resolve_right (exp_ne_zero _)
  convert hg.neg.div hf hf0 using 1
  field_simp [hf0]
  linear_combination -(f z) * hnum

theorem coefficients_differentiableAt (l : ℕ) (n z : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (cPlus l n) z ∧ DifferentiableAt ℂ (cMinus l n) z := by
  have hnz : n * z ≠ 0 := mul_ne_zero hn hz
  have hp : DifferentiableAt ℂ (p l) z :=
    (hankelPoly_hasDerivAt l I z hz).differentiableAt
  have hpd : DifferentiableAt ℂ (pD l) z :=
    (hankelPolyD_hasDerivAt l I z hz).differentiableAt
  have hpn : DifferentiableAt ℂ (p l) (n * z) :=
    (hankelPoly_hasDerivAt l I (n * z) hnz).differentiableAt
  have hpdn : DifferentiableAt ℂ (pD l) (n * z) :=
    (hankelPolyD_hasDerivAt l I (n * z) hnz).differentiableAt
  have hmn : DifferentiableAt ℂ (pMinus l) (n * z) :=
    (hankelPoly_hasDerivAt l (-I) (n * z) hnz).differentiableAt
  have hmdn : DifferentiableAt ℂ (pMinusD l) (n * z) :=
    (hankelPolyD_hasDerivAt l (-I) (n * z) hnz).differentiableAt
  constructor
  · unfold cPlus
    fun_prop
  · unfold cMinus
    fun_prop

def expSum (a : ℂ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * exp (a * z) + g z * exp (-a * z)

theorem expSum_hasDerivAt (f g : ℂ → ℂ) (f' g' a z : ℂ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) :
    HasDerivAt (expSum a f g)
      ((f' + a * f z) * exp (a * z) +
       (g' - a * g z) * exp (-a * z)) z := by
  have hp : HasDerivAt (fun w : ℂ => exp (a * w)) (exp (a * z) * a) z :=
    by simpa using ((hasDerivAt_id z).const_mul a).cexp
  have hm : HasDerivAt (fun w : ℂ => exp (-a * w)) (exp (-a * z) * (-a)) z :=
    by simpa using ((hasDerivAt_id z).const_mul (-a)).cexp
  convert (hf.mul hp).add (hg.mul hm) using 1 <;> first | rfl | ring

/-- For the actual finite Hankel determinant, simultaneous vanishing of
the determinant and its complex derivative forces the rational equation
used in the multiplicity argument. No pole-simplicity assumption occurs. -/
theorem multiple_tm_zero_forces_rational_derivative
    (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hcp : cPlus l n z ≠ 0) (hd : tmDet l n z = 0)
    (hdd : deriv (tmDet l n) z = 0) :
    deriv (rationalPole l n) z = 2 * I * n * rationalPole l n z := by
  let a : ℂ := I * n
  let f : ℂ → ℂ := cPlus l n
  let g : ℂ → ℂ := cMinus l n
  let b : ℂ → ℂ := fun w => (-I) ^ (l + 1) * exp (I * w) / 2
  let b' : ℂ := (-I) ^ (l + 1) * (exp (I * z) * I) / 2
  let e' : ℂ := (deriv f z + a * f z) * exp (a * z) +
    (deriv g z - a * g z) * exp (-a * z)
  have hc := coefficients_differentiableAt l n z hn hz
  have hf : HasDerivAt f (deriv f z) z := hc.1.hasDerivAt
  have hg : HasDerivAt g (deriv g z) z := hc.2.hasDerivAt
  have he : HasDerivAt (expSum a f g) e' z :=
    expSum_hasDerivAt f g _ _ a z hf hg
  have hb : HasDerivAt b b' z := by
    have h : HasDerivAt (fun w : ℂ => exp (I * w)) (exp (I * z) * I) z :=
      by simpa using ((hasDerivAt_id z).const_mul I).cexp
    exact (h.const_mul ((-I) ^ (l + 1))).div_const 2
  have hfun : tmDet l n = fun w => b w * expSum a f g w := by
    funext w
    simpa only [b, a, f, g, expSum, mul_assoc, neg_mul] using
      tmDet_exp_factorization l n w
  have hb0 : b z ≠ 0 := determinant_prefactor_ne_zero l z
  have he0 : expSum a f g z = 0 := by
    rw [hfun] at hd
    exact (mul_eq_zero.mp hd).resolve_left hb0
  have hprod := hb.mul he
  rw [← hfun] at hprod
  have hderiv := hprod.deriv
  rw [hdd, he0, mul_zero, zero_add] at hderiv
  have he' : e' = 0 := (mul_eq_zero.mp hderiv.symm).resolve_left hb0
  have hratio := quotient_derivative_of_double_exp_zero f g _ _ a z hf hg hcp he0 he'
  have hr : deriv (rationalPole l n) z = 2 * a * rationalPole l n z :=
    hratio.deriv
  rw [hr]
  dsimp [a]
  ring

theorem p_one (z : ℂ) : p 1 z = 1 + I / z := by
  norm_num [p, hankelPoly, hankelCoeff, Finset.sum_range_succ, div_eq_mul_inv]
  left
  ring

theorem pMinus_one (z : ℂ) : pMinus 1 z = 1 - I / z := by
  norm_num [pMinus, hankelPoly, hankelCoeff, Finset.sum_range_succ,
    div_eq_mul_inv, sub_eq_add_neg]
  left
  ring

theorem pD_one (z : ℂ) : pD 1 z = -I / z ^ 2 := by
  norm_num [pD, hankelPolyD, hankelCoeff, Finset.sum_range_succ, div_eq_mul_inv]
  simp [inv_pow]
  rfl

theorem pMinusD_one (z : ℂ) : pMinusD 1 z = I / z ^ 2 := by
  norm_num [pMinusD, hankelPolyD, hankelCoeff, Finset.sum_range_succ,
    div_eq_mul_inv]
  simp [inv_pow]
  rfl

/-- The base l=1 outgoing/incoming Riccati pair has its exact nonzero
Wronskian, certified from the explicit finite formula. -/
theorem l_one_wronskian (z : ℂ) (hz : z ≠ 0) :
    xi 1 z * xiMinusD 1 z - xiMinus 1 z * xiD 1 z = -2 * I := by
  have he : exp (I * z) * exp (-I * z) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1 <;> congr 1 <;> ring
  have ha : (1 + I / z) * (-I * (1 - I / z) + I / z ^ 2) -
      (1 - I / z) * (I * (1 + I / z) - I / z ^ 2) = -2 * I := by
    field_simp [hz]
    ring_nf
    norm_num [pow_succ, I_sq]
    ring
  calc
    xi 1 z * xiMinusD 1 z - xiMinus 1 z * xiD 1 z =
        (exp (I * z) * exp (-I * z)) *
        ((1 + I / z) * (-I * (1 - I / z) + I / z ^ 2) -
          (1 - I / z) * (I * (1 + I / z) - I / z ^ 2)) := by
      unfold xi xiD xiMinus xiMinusD
      rw [p_one, pMinus_one, pD_one, pMinusD_one]
      norm_num
      ring
    _ = -2 * I := by rw [he, ha, one_mul]

theorem matching_plus_factor (l : ℕ) (n z : ℂ) :
    n * xi l (n * z) * xiD l z - xi l z * xiD l (n * z) =
      (-I) ^ (l + 1) * exp (I * z) * cPlus l n z * exp (I * (n * z)) := by
  unfold xi xiD cPlus
  ring

theorem matching_minus_factor (l : ℕ) (n z : ℂ) :
    n * xiMinus l (n * z) * xiD l z - xi l z * xiMinusD l (n * z) =
      (-I) ^ (l + 1) * exp (I * z) * cMinus l n z * exp (-I * (n * z)) := by
  unfold xi xiD xiMinus xiMinusD cMinus
  ring

theorem l_one_coefficients_not_both_zero (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    ¬(cPlus 1 n z = 0 ∧ cMinus 1 n z = 0) := by
  have hnz : n * z ≠ 0 := mul_ne_zero hn hz
  have hw : xi 1 (n * z) * xiMinusD 1 (n * z) -
      xiMinus 1 (n * z) * xiD 1 (n * z) ≠ 0 := by
    rw [l_one_wronskian _ hnz]
    norm_num
  have hx : xi 1 z ≠ 0 ∨ xiD 1 z ≠ 0 := by
    by_cases hx : xi 1 z = 0
    · right
      intro hdx
      have h := l_one_wronskian z hz
      rw [hx, hdx] at h
      norm_num at h
    · exact Or.inl hx
  have hnot := matching_pair_not_both_zero n (xi 1 (n * z)) (xiMinus 1 (n * z))
    (xiD 1 (n * z)) (xiMinusD 1 (n * z)) (xi 1 z) (xiD 1 z) hn hw hx
  rintro ⟨hp, hm⟩
  apply hnot
  constructor
  · rw [matching_plus_factor, hp]
    ring
  · rw [matching_minus_factor, hm]
    ring

/-- In the actual base degree, nonzero matching coefficients are proved
from the exact Wronskian rather than supplied as a pole hypothesis. -/
theorem l_one_plus_ne_zero_at_pole (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet 1 n z = 0) : cPlus 1 n z ≠ 0 := by
  intro hp
  rw [tmDet_exp_factorization] at hd
  have hs := (mul_eq_zero.mp hd).resolve_left (determinant_prefactor_ne_zero 1 z)
  rw [hp, zero_mul, zero_add] at hs
  have hm := (mul_eq_zero.mp hs).resolve_right (exp_ne_zero _)
  exact l_one_coefficients_not_both_zero n z hn hz ⟨hp, hm⟩

theorem l_one_multiple_zero_rational_condition (n z : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) (hd : tmDet 1 n z = 0)
    (hdd : deriv (tmDet 1 n) z = 0) :
    exp (2 * I * n * z) = rationalPole 1 n z ∧
    deriv (rationalPole 1 n) z = 2 * I * n * rationalPole 1 n z := by
  have hp := l_one_plus_ne_zero_at_pole n z hn hz hd
  exact ⟨(tmDet_zero_iff_exp 1 n z hp).1 hd,
    multiple_tm_zero_forces_rational_derivative 1 n z hn hz hp hd hdd⟩

end OQ14.ModalAlgebra

#print axioms OQ14.ModalAlgebra.hankelPoly_hasDerivAt
#print axioms OQ14.ModalAlgebra.hankelPolyD_hasDerivAt
#print axioms OQ14.ModalAlgebra.xi_hasDerivAt
#print axioms OQ14.ModalAlgebra.xiMinus_hasDerivAt
#print axioms OQ14.ModalAlgebra.psi_hasDerivAt
#print axioms OQ14.ModalAlgebra.tmDet_exp_factorization
#print axioms OQ14.ModalAlgebra.determinant_prefactor_ne_zero
#print axioms OQ14.ModalAlgebra.exp_double_split
#print axioms OQ14.ModalAlgebra.tmDet_zero_iff_exp
#print axioms OQ14.ModalAlgebra.minus_ne_zero_at_pole
#print axioms OQ14.ModalAlgebra.matching_pair_not_both_zero
#print axioms OQ14.ModalAlgebra.quotient_derivative_of_double_exp_zero
#print axioms OQ14.ModalAlgebra.coefficients_differentiableAt
#print axioms OQ14.ModalAlgebra.expSum_hasDerivAt
#print axioms OQ14.ModalAlgebra.multiple_tm_zero_forces_rational_derivative
#print axioms OQ14.ModalAlgebra.p_one
#print axioms OQ14.ModalAlgebra.pMinus_one
#print axioms OQ14.ModalAlgebra.pD_one
#print axioms OQ14.ModalAlgebra.pMinusD_one
#print axioms OQ14.ModalAlgebra.l_one_wronskian
#print axioms OQ14.ModalAlgebra.matching_plus_factor
#print axioms OQ14.ModalAlgebra.matching_minus_factor
#print axioms OQ14.ModalAlgebra.l_one_coefficients_not_both_zero
#print axioms OQ14.ModalAlgebra.l_one_plus_ne_zero_at_pole
#print axioms OQ14.ModalAlgebra.l_one_multiple_zero_rational_condition

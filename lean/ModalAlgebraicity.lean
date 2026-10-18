import ModalRational
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Algebraicity of exceptional spherical TM poles

The explicit finite polynomials are lifted to the actual subalgebra of
complex numbers algebraic over the rationals. Their nonzero roots are
algebraic by transitivity. No exponential transcendence principle is
introduced as an axiom or inferred from this algebraic step.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalAlgebraicity

open Complex Polynomial OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.ModalRational

abbrev AlgNumbers := Subalgebra.algebraicClosure ℚ ℂ

def AlgebraicPolynomial (p : Polynomial ℂ) : Prop :=
  ∃ q : Polynomial AlgNumbers, q.map (algebraMap AlgNumbers ℂ) = p

theorem algebraic_I : IsAlgebraic ℚ (I : ℂ) := by
  refine ⟨X ^ 2 + 1, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
    norm_num [coeff_one] at hc
  · norm_num

theorem algebraicPolynomial_C (c : ℂ) (hc : IsAlgebraic ℚ c) :
    AlgebraicPolynomial (C c) := by
  refine ⟨C (⟨c, hc⟩ : AlgNumbers), ?_⟩
  simp
  rfl

theorem algebraicPolynomial_X : AlgebraicPolynomial (X : Polynomial ℂ) :=
  ⟨X, by simp⟩

theorem algebraicPolynomial_add {p q : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) (hq : AlgebraicPolynomial q) :
    AlgebraicPolynomial (p + q) := by
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  exact ⟨p' + q', by simp⟩

theorem algebraicPolynomial_sub {p q : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) (hq : AlgebraicPolynomial q) :
    AlgebraicPolynomial (p - q) := by
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  exact ⟨p' - q', by simp⟩

theorem algebraicPolynomial_mul {p q : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) (hq : AlgebraicPolynomial q) :
    AlgebraicPolynomial (p * q) := by
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  exact ⟨p' * q', by simp⟩

theorem algebraicPolynomial_pow {p : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) (s : ℕ) : AlgebraicPolynomial (p ^ s) := by
  obtain ⟨p', rfl⟩ := hp
  exact ⟨p' ^ s, by simp⟩

theorem algebraicPolynomial_comp {p q : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) (hq : AlgebraicPolynomial q) :
    AlgebraicPolynomial (p.comp q) := by
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  exact ⟨p'.comp q', by rw [map_comp]⟩

theorem algebraicPolynomial_derivative {p : Polynomial ℂ}
    (hp : AlgebraicPolynomial p) : AlgebraicPolynomial p.derivative := by
  obtain ⟨p', rfl⟩ := hp
  exact ⟨p'.derivative, (derivative_map _ _).symm⟩

theorem algebraicPolynomial_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ)
    (hp : ∀ i ∈ s, AlgebraicPolynomial (p i)) :
    AlgebraicPolynomial (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact algebraicPolynomial_add (hp a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hp i (Finset.mem_insert_of_mem hi)))

theorem algebraicPolynomial_root {p : Polynomial ℂ} (hp : AlgebraicPolynomial p)
    (hp0 : p ≠ 0) (z : ℂ) (hz : p.eval z = 0) : IsAlgebraic ℚ z := by
  obtain ⟨q, hq⟩ := hp
  have hq0 : q ≠ 0 := by
    intro h
    apply hp0
    rw [← hq, h, Polynomial.map_zero]
  have hzq : IsAlgebraic AlgNumbers z := by
    refine ⟨q, hq0, ?_⟩
    rw [← eval_map_algebraMap, hq]
    exact hz
  exact hzq.restrictScalars ℚ

theorem algebraicPolynomial_eval {p : Polynomial ℂ} (hp : AlgebraicPolynomial p)
    (z : ℂ) (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (p.eval z) := by
  obtain ⟨q, hq⟩ := hp
  let za : AlgNumbers := ⟨z, hz⟩
  have hv : IsAlgebraic ℚ ((q.eval za : AlgNumbers) : ℂ) := (q.eval za).property
  have he : ((q.eval za : AlgNumbers) : ℂ) = p.eval z := by
    rw [← hq, eval_map]
    exact (eval₂_at_apply (algebraMap AlgNumbers ℂ) za).symm
  rwa [he] at hv

theorem algebraic_hankelCoeff (l s : ℕ) (phase : ℂ) (hp : IsAlgebraic ℚ phase) :
    IsAlgebraic ℚ (hankelCoeff l s phase) := by
  unfold hankelCoeff
  rw [div_eq_mul_inv]
  exact ((hp.pow s).mul (isAlgebraic_nat (Nat.factorial (l + s)))).mul
    ((((isAlgebraic_nat 2).pow s).mul (isAlgebraic_nat (Nat.factorial s))).mul
      (isAlgebraic_nat (Nat.factorial (l - s)))).inv

theorem algebraic_inversePolynomial (l : ℕ) (phase : ℂ) (hp : IsAlgebraic ℚ phase) :
    AlgebraicPolynomial (inversePolynomial l phase) := by
  apply algebraicPolynomial_sum
  intro s _
  exact algebraicPolynomial_mul (algebraicPolynomial_C _ (algebraic_hankelCoeff l s phase hp))
    (algebraicPolynomial_pow algebraicPolynomial_X s)

theorem algebraic_plusPolynomial (l : ℕ) (n : ℂ) (hn : IsAlgebraic ℚ n) :
    AlgebraicPolynomial (plusPolynomial l n) := by
  have hq := algebraic_inversePolynomial l I algebraic_I
  have hs := algebraicPolynomial_mul (algebraicPolynomial_C _ hn.inv) algebraicPolynomial_X
  have hqn := algebraicPolynomial_comp hq hs
  have hd := algebraicPolynomial_derivative hq
  have hdn := algebraicPolynomial_comp hd hs
  unfold plusPolynomial
  exact algebraicPolynomial_mul (algebraicPolynomial_C _ (algebraic_I.neg.pow _))
    (algebraicPolynomial_add
      (algebraicPolynomial_sub
        (algebraicPolynomial_mul
          (algebraicPolynomial_mul
            (algebraicPolynomial_C _ (algebraic_I.mul (hn.sub isAlgebraic_one))) hq) hqn)
        (algebraicPolynomial_mul
          (algebraicPolynomial_mul
            (algebraicPolynomial_mul (algebraicPolynomial_C _ hn)
              (algebraicPolynomial_pow algebraicPolynomial_X 2)) hqn) hd))
      (algebraicPolynomial_mul
        (algebraicPolynomial_mul (algebraicPolynomial_pow hs 2) hq) hdn))

theorem algebraic_minusPolynomial (l : ℕ) (n : ℂ) (hn : IsAlgebraic ℚ n) :
    AlgebraicPolynomial (minusPolynomial l n) := by
  have hq := algebraic_inversePolynomial l I algebraic_I
  have hm := algebraic_inversePolynomial l (-I) algebraic_I.neg
  have hs := algebraicPolynomial_mul (algebraicPolynomial_C _ hn.inv) algebraicPolynomial_X
  have hmn := algebraicPolynomial_comp hm hs
  have hd := algebraicPolynomial_derivative hq
  have hmdn := algebraicPolynomial_comp (algebraicPolynomial_derivative hm) hs
  unfold minusPolynomial
  exact algebraicPolynomial_mul (algebraicPolynomial_C _ (algebraic_I.pow _))
    (algebraicPolynomial_add
      (algebraicPolynomial_sub
        (algebraicPolynomial_mul
          (algebraicPolynomial_mul
            (algebraicPolynomial_C _ (algebraic_I.mul (hn.add isAlgebraic_one))) hq) hmn)
        (algebraicPolynomial_mul
          (algebraicPolynomial_mul
            (algebraicPolynomial_mul (algebraicPolynomial_C _ hn)
              (algebraicPolynomial_pow algebraicPolynomial_X 2)) hmn) hd))
      (algebraicPolynomial_mul
        (algebraicPolynomial_mul (algebraicPolynomial_pow hs 2) hq) hmdn))

theorem algebraic_multiplicityPolynomial (l : ℕ) (n : ℂ) (hn : IsAlgebraic ℚ n) :
    AlgebraicPolynomial (multiplicityPolynomial l n) := by
  have ha := algebraic_plusPolynomial l n hn
  have hb := algebraic_minusPolynomial l n hn
  exact algebraicPolynomial_add
    (algebraicPolynomial_mul (algebraicPolynomial_pow algebraicPolynomial_X 2)
      (algebraicPolynomial_sub
        (algebraicPolynomial_mul (algebraicPolynomial_derivative hb) ha)
        (algebraicPolynomial_mul hb (algebraicPolynomial_derivative ha))))
    (algebraicPolynomial_mul
      (algebraicPolynomial_mul
        (algebraicPolynomial_C _ (((isAlgebraic_nat 2).mul algebraic_I).mul hn)) hb) ha)

theorem algebraic_separationPolynomial (l j : ℕ) (n : ℂ) (hn : IsAlgebraic ℚ n) :
    AlgebraicPolynomial (separationPolynomial l j n) :=
  algebraicPolynomial_sub
    (algebraicPolynomial_mul (algebraic_plusPolynomial l n hn) (algebraic_minusPolynomial j n hn))
    (algebraicPolynomial_mul (algebraic_plusPolynomial j n hn) (algebraic_minusPolynomial l n hn))

/-- Every hypothetical multiple nonzero TM determinant zero is algebraic
when the index n is algebraic and outside 0,+1,-1. -/
theorem multiple_zero_isAlgebraic (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hd : tmDet l n z = 0) (hdd : deriv (tmDet l n) z = 0) :
    IsAlgebraic ℚ z := by
  have hi := algebraicPolynomial_root (algebraic_multiplicityPolynomial l n hna)
    (multiplicityPolynomial_ne_zero l n hn hp hm) z⁻¹
    (multiple_zero_is_polynomial_root l n z hn hz hd hdd)
  simpa using hi.inv

/-- Every hypothetical common nonzero TM determinant zero of distinct
degrees is algebraic for an algebraic index n outside 0,+1,-1. -/
theorem common_zero_isAlgebraic (l j : ℕ) (n z : ℂ)
    (hlj : l ≠ j) (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hl : tmDet l n z = 0) (hj : tmDet j n z = 0) :
    IsAlgebraic ℚ z := by
  have hi := algebraicPolynomial_root (algebraic_separationPolynomial l j n hna)
    (separationPolynomial_ne_zero l j n hlj hn hp hm) z⁻¹
    (common_zero_is_polynomial_root l j n z hn hz hl hj)
  simpa using hi.inv

theorem rationalPole_isAlgebraic (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hza : IsAlgebraic ℚ z) (hn : n ≠ 0) (hz : z ≠ 0) :
    IsAlgebraic ℚ (rationalPole l n z) := by
  have he : rationalPole l n z =
      -(minusPolynomial l n).eval z⁻¹ / (plusPolynomial l n).eval z⁻¹ := by
    simpa using rationalPole_inverse l n z⁻¹ hn (inv_ne_zero hz)
  rw [he, div_eq_mul_inv]
  exact (algebraicPolynomial_eval (algebraic_minusPolynomial l n hna) z⁻¹ hza.inv).neg.mul
    (algebraicPolynomial_eval (algebraic_plusPolynomial l n hna) z⁻¹ hza.inv).inv

/-- An algebraic nonzero pole would make the exponential of a nonzero
algebraic number algebraic. The missing transcendence step is deliberately
not a premise or an axiom of this theorem. -/
theorem algebraic_pole_exponential_obstruction (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hza : IsAlgebraic ℚ z)
    (hn : n ≠ 0) (hz : z ≠ 0) (hd : tmDet l n z = 0) :
    IsAlgebraic ℚ (2 * I * n * z) ∧ 2 * I * n * z ≠ 0 ∧
      IsAlgebraic ℚ (exp (2 * I * n * z)) := by
  refine ⟨(((isAlgebraic_nat 2).mul algebraic_I).mul hna).mul hza, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn) hz
  · rw [(tmDet_zero_iff_exp l n z (plus_ne_zero_at_pole l n z hn hz hd)).mp hd]
    exact rationalPole_isAlgebraic l n z hna hza hn hz

theorem multiple_zero_exponential_obstruction (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hd : tmDet l n z = 0) (hdd : deriv (tmDet l n) z = 0) :
    IsAlgebraic ℚ (2 * I * n * z) ∧ 2 * I * n * z ≠ 0 ∧
      IsAlgebraic ℚ (exp (2 * I * n * z)) :=
  algebraic_pole_exponential_obstruction l n z hna
    (multiple_zero_isAlgebraic l n z hna hn hp hm hz hd hdd) hn hz hd

theorem common_zero_exponential_obstruction (l j : ℕ) (n z : ℂ)
    (hlj : l ≠ j) (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hl : tmDet l n z = 0) (hj : tmDet j n z = 0) :
    IsAlgebraic ℚ (2 * I * n * z) ∧ 2 * I * n * z ≠ 0 ∧
      IsAlgebraic ℚ (exp (2 * I * n * z)) :=
  algebraic_pole_exponential_obstruction l n z hna
    (common_zero_isAlgebraic l j n z hlj hna hn hp hm hz hl hj) hn hz hl

end OQ14.ModalAlgebraicity

#print axioms OQ14.ModalAlgebraicity.algebraic_I
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_C
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_X
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_add
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_sub
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_mul
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_pow
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_comp
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_derivative
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_sum
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_root
#print axioms OQ14.ModalAlgebraicity.algebraicPolynomial_eval
#print axioms OQ14.ModalAlgebraicity.algebraic_hankelCoeff
#print axioms OQ14.ModalAlgebraicity.algebraic_inversePolynomial
#print axioms OQ14.ModalAlgebraicity.algebraic_plusPolynomial
#print axioms OQ14.ModalAlgebraicity.algebraic_minusPolynomial
#print axioms OQ14.ModalAlgebraicity.algebraic_multiplicityPolynomial
#print axioms OQ14.ModalAlgebraicity.algebraic_separationPolynomial
#print axioms OQ14.ModalAlgebraicity.multiple_zero_isAlgebraic
#print axioms OQ14.ModalAlgebraicity.common_zero_isAlgebraic
#print axioms OQ14.ModalAlgebraicity.rationalPole_isAlgebraic
#print axioms OQ14.ModalAlgebraicity.algebraic_pole_exponential_obstruction
#print axioms OQ14.ModalAlgebraicity.multiple_zero_exponential_obstruction
#print axioms OQ14.ModalAlgebraicity.common_zero_exponential_obstruction

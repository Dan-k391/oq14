import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed

/-! Actual entire scalar power series from a factorial coefficient bound. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.EntireFactorialSeries

open Complex Set Metric

def term (a : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ := a m*z^m
def rawD (a : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ := a m*(m : ℕ)*z^(m-1)
def shift (a : ℕ → ℂ) (m : ℕ) : ℂ := a (m+1)*(m+1 : ℕ)
def sum (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' m : ℕ, term a m z

theorem term_bound (a : ℕ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ)))
    (m : ℕ) (z : ℂ) (hz : ‖z‖ ≤ B) :
    ‖term a m z‖ ≤ A*((B/2)^m/(m.factorial : ℝ)) := by
  simp only [term,norm_mul,norm_pow]
  have h := mul_le_mul (ha m) (pow_le_pow_left₀ (norm_nonneg z) hz m)
    (pow_nonneg (norm_nonneg z) _) (by positivity)
  convert h using 1
  rw [div_pow]
  field_simp

theorem terms_summable (a : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ))) (z : ℂ) :
    Summable (fun m : ℕ => term a m z) :=
  Summable.of_norm_bounded _ ((Real.summable_pow_div_factorial (‖z‖/2)).mul_left A)
    (fun m => term_bound a A ‖z‖ hA (norm_nonneg z) ha m z le_rfl)

theorem rawD_bound (a : ℕ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ)))
    (m : ℕ) (z : ℂ) (hz : ‖z‖ ≤ B) :
    ‖rawD a m z‖ ≤ A*(B^m/(m.factorial : ℝ)) := by
  have hm : (m : ℝ) ≤ 2^m := by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hp : ‖z‖^(m-1) ≤ B^m :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans (pow_le_pow_right₀ hB (Nat.sub_le m 1))
  simp only [rawD,norm_mul,norm_pow,Complex.norm_natCast]
  have hcoeff := mul_le_mul (ha m) hm (by positivity : 0 ≤ (m : ℝ)) (by positivity)
  have h := mul_le_mul hcoeff hp (by positivity) (by positivity)
  convert h using 1
  field_simp
  ring

theorem rawD_summable (a : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ))) (z : ℂ) :
    Summable (fun m : ℕ => rawD a m z) := by
  let B : ℝ := ‖z‖+1
  have hB : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg z]
  exact Summable.of_norm_bounded _ ((Real.summable_pow_div_factorial B).mul_left A)
    (fun m => rawD_bound a A B hA hB ha m z (by dsimp [B]; linarith))

theorem rawD_sum_eq (a : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ))) (z : ℂ) :
    (∑' m : ℕ, rawD a m z) = sum (shift a) z := by
  rw [(rawD_summable a A hA ha z).tsum_eq_zero_add]
  simp only [rawD,Nat.cast_zero,mul_zero,zero_mul,zero_add,Nat.add_sub_cancel_right]
  rfl

theorem sum_hasDerivAt (a : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ))) (z : ℂ) :
    HasDerivAt (sum a) (sum (shift a) z) z := by
  let B : ℝ := ‖z‖+1
  have hB : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg z]
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have h : HasDerivAt (sum a) (∑' m : ℕ, rawD a m z) z := by
    apply hasDerivAt_tsum_of_isPreconnected
      (g := term a) (g' := rawD a) (y₀ := (0 : ℂ))
      (u := fun m : ℕ => A*(B^m/(m.factorial : ℝ)))
      ((Real.summable_pow_div_factorial B).mul_left A)
      isOpen_ball (convex_ball (0 : ℂ) B).isPreconnected
    · intro m u _
      simpa only [term,rawD,mul_assoc] using (hasDerivAt_pow m u).const_mul (a m)
    · intro m u hu
      exact rawD_bound a A B hA hB ha m u (mem_ball_zero_iff.mp hu).le
    · exact mem_ball_self hBp
    · exact terms_summable a A hA ha 0
    · apply mem_ball_zero_iff.mpr
      dsimp [B]
      linarith
  rw [rawD_sum_eq a A hA ha z] at h
  exact h

theorem sum_analyticAt (a : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ m : ℕ, ‖a m‖ ≤ A/(2^m*(m.factorial : ℝ))) (z : ℂ) : AnalyticAt ℂ (sum a) z := by
  have hd : Differentiable ℂ (sum a) := fun w => (sum_hasDerivAt a A hA ha w).differentiableAt
  exact hd.analyticAt z

end OQ14.EntireFactorialSeries

#print axioms OQ14.EntireFactorialSeries.term_bound
#print axioms OQ14.EntireFactorialSeries.terms_summable
#print axioms OQ14.EntireFactorialSeries.rawD_bound
#print axioms OQ14.EntireFactorialSeries.rawD_summable
#print axioms OQ14.EntireFactorialSeries.rawD_sum_eq
#print axioms OQ14.EntireFactorialSeries.sum_hasDerivAt
#print axioms OQ14.EntireFactorialSeries.sum_analyticAt

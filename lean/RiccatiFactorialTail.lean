import RiccatiCompactDerivatives
import Mathlib.Analysis.Normed.Group.Tannery

/-! Actual regular amplitudes absorb every fixed exponential degree weight. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RiccatiFactorialTail

open Filter OQ14.RiccatiSeriesCoefficients
open scoped Topology Nat

theorem factorial_le_odd_doubleFactorial (l : ℕ) : l.factorial ≤ (2*l+1)‼ := by
  induction l with
  | zero => norm_num
  | succ l ih =>
    rw [show 2*(l+1)+1=(2*l+1)+2 by omega,Nat.doubleFactorial_add_two,Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

theorem amplitude_factorial_bound (l : ℕ) : amplitude l 0 ≤ 1/(l.factorial : ℝ) := by
  rw [RiccatiGaussianBound.amplitude_doubleFactorial]
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (by exact_mod_cast factorial_le_odd_doubleFactorial l)

theorem successor_le_two_pow (l : ℕ) : (l+1 : ℝ) ≤ 2^l := by
  induction l with
  | zero => norm_num
  | succ l ih =>
    rw [pow_succ]
    push_cast
    linarith [show (0 : ℝ) ≤ l from Nat.cast_nonneg l]

theorem weighted_amplitude_bound (l k : ℕ) (b K : ℝ) (_hb : 0 ≤ b) :
    (l+1 : ℝ)^k*Real.exp (K*(l : ℝ))*(amplitude l 0*b^(l+1))^2 ≤
      b^2*((2^k*Real.exp K*b^2)^l/(l.factorial : ℝ)) := by
  have hfac : 1 ≤ (l.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos l
  have hA : 0 ≤ amplitude l 0 := (amplitude_pos l 0).le
  have hamp := amplitude_factorial_bound l
  have hsquare : (amplitude l 0)^2 ≤ 1/(l.factorial : ℝ) := by
    have hsq := pow_le_pow_left₀ hA hamp 2
    have hden : (1/(l.factorial : ℝ))^2 ≤ 1/(l.factorial : ℝ) := by
      have hinv : 0 ≤ 1/(l.factorial : ℝ) := by positivity
      have hle : 1/(l.factorial : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hfac
      nlinarith
    exact hsq.trans hden
  have hw : (l+1 : ℝ)^k ≤ (2^k : ℝ)^l := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (l+1 : ℝ)) (successor_le_two_pow l) k
    simpa only [← pow_mul,Nat.mul_comm] using h
  have he : Real.exp (K*(l : ℝ)) = (Real.exp K)^l := by
    rw [mul_comm,Real.exp_nat_mul]
  have hnorm : (amplitude l 0*b^(l+1))^2 ≤ b^2*(b^2)^l/(l.factorial : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hsquare (by positivity : 0 ≤ (b^(l+1))^2)
    have heq : (b^(l+1))^2 = b^2*(b^2)^l := by
      rw [show b^(l+1)=b^l*b from pow_succ b l,mul_pow,pow_right_comm b l 2]
      ring
    rw [mul_pow,heq]
    convert h using 1
    · rw [heq]
    · rw [heq]
      ring
  have h := mul_le_mul (mul_le_mul_of_nonneg_right hw (Real.exp_pos (K*(l : ℝ))).le) hnorm
    (sq_nonneg _) (by positivity)
  convert h using 1
  rw [he,mul_pow,mul_pow]
  ring

theorem weighted_amplitudes_summable (k : ℕ) (b K : ℝ) (hb : 0 ≤ b) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*Real.exp (K*(l : ℝ))*(amplitude l 0*b^(l+1))^2) := by
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun l => weighted_amplitude_bound l k b K hb)
    ((Real.summable_pow_div_factorial (2^k*Real.exp K*b^2)).mul_left (b^2))

def movingTail (G : ℕ → ℝ) (R : ℝ) : ℝ := ∑' l : ℕ, if R ≤ 4*(l : ℝ) then G l else 0

theorem movingTail_tendsto_zero (G : ℕ → ℝ) (hG : Summable G) :
    Tendsto (movingTail G) atTop (𝓝 0) := by
  have hlim : ∀ l : ℕ, Tendsto (fun R : ℝ => if R ≤ 4*(l : ℝ) then G l else 0) atTop (𝓝 0) := by
    intro l
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (4*(l : ℝ))] with R hR
    simp only [not_le.mpr hR,ite_false]
  have h := tendsto_tsum_of_dominated_convergence hG.abs hlim
    (Filter.Eventually.of_forall (fun R l => by split_ifs <;> simp))
  simpa only [movingTail,tsum_zero] using h

theorem movingTail_nonnegative (G : ℕ → ℝ) (hG : ∀ l, 0 ≤ G l) (R : ℝ) :
    0 ≤ movingTail G R := by
  apply tsum_nonneg
  intro l
  split_ifs
  · exact hG l
  · exact le_rfl

end OQ14.RiccatiFactorialTail

#print axioms OQ14.RiccatiFactorialTail.factorial_le_odd_doubleFactorial
#print axioms OQ14.RiccatiFactorialTail.amplitude_factorial_bound
#print axioms OQ14.RiccatiFactorialTail.successor_le_two_pow
#print axioms OQ14.RiccatiFactorialTail.weighted_amplitude_bound
#print axioms OQ14.RiccatiFactorialTail.weighted_amplitudes_summable
#print axioms OQ14.RiccatiFactorialTail.movingTail_tendsto_zero
#print axioms OQ14.RiccatiFactorialTail.movingTail_nonnegative

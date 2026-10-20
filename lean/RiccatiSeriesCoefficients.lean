import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.SmoothSeries
import HankelPolynomial

/-! # Actual convergent regular Riccati series coefficients -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.RiccatiSeriesCoefficients

open Filter Set
open scoped Topology

def amplitude (l m : ℕ) : ℝ :=
  2^l*(Nat.factorial (l+m) : ℝ)/((Nat.factorial m : ℝ)*(Nat.factorial (2*(l+m)+1) : ℝ))

def coeff (l m : ℕ) : ℝ := (-1)^m*amplitude l m

theorem amplitude_pos (l m : ℕ) : 0 < amplitude l m := by
  unfold amplitude
  positivity

theorem amplitude_zero_degree (m : ℕ) : amplitude 0 m = 1/(Nat.factorial (2*m+1) : ℝ) := by
  simp only [amplitude,pow_zero,Nat.zero_add,one_mul]
  field_simp

theorem amplitude_raising (l m : ℕ) : amplitude (l+1) m = 2*(m+1)*amplitude l (m+1) := by
  have hfac : (Nat.factorial (m+1) : ℝ) = (m+1 : ℝ)*(Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold amplitude
  rw [show l+1+m=l+(m+1) by omega,pow_succ,hfac]
  field_simp
  ring

theorem coeff_raising (l m : ℕ) : coeff (l+1) m = -2*(m+1)*coeff l (m+1) := by
  rw [coeff,coeff,amplitude_raising,pow_succ]
  ring

theorem amplitude_recurrence (l m : ℕ) :
    2*(m+1)*(2*(l+m)+3)*amplitude l (m+1) = amplitude l m := by
  have hfacN : (Nat.factorial (l+m+1) : ℝ) =
      (l+m+1 : ℝ)*(Nat.factorial (l+m) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfacM : (Nat.factorial (m+1) : ℝ) = (m+1 : ℝ)*(Nat.factorial m : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfacB : (Nat.factorial (2*(l+m)+1+2) : ℝ) =
      (2*(l+m)+3 : ℝ)*(2*(l+m)+2)*(Nat.factorial (2*(l+m)+1) : ℝ) := by
    rw [Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  unfold amplitude
  rw [show l+(m+1)=l+m+1 by omega,show 2*(l+m+1)+1=2*(l+m)+1+2 by omega,
    hfacN,hfacM,hfacB]
  field_simp
  ring

theorem amplitude_factorial_bound (l m : ℕ) :
    2^m*(Nat.factorial m : ℝ)*amplitude l m ≤ amplitude l 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hn := amplitude_pos l (m+1)
    have hr := amplitude_recurrence l m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hh : 2*(m+1 : ℝ)*amplitude l (m+1) ≤ amplitude l m := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2*(m+1)) hn.le]
    calc
      _ = (2^m*(Nat.factorial m : ℝ))*(2*(m+1)*amplitude l (m+1)) := by
        rw [pow_succ,Nat.factorial_succ]
        push_cast
        ring
      _ ≤ (2^m*(Nat.factorial m : ℝ))*amplitude l m :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := ih

theorem amplitude_le_majorant (l m : ℕ) :
    amplitude l m ≤ amplitude l 0/(2^m*(Nat.factorial m : ℝ)) := by
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^m*(Nat.factorial m : ℝ))).mpr
  simpa only [mul_comm,mul_left_comm,mul_assoc] using amplitude_factorial_bound l m

theorem coeff_abs (l m : ℕ) : |coeff l m| = amplitude l m := by
  rw [coeff,abs_mul,abs_pow,abs_of_pos (amplitude_pos l m)]
  norm_num

theorem power_majorant (l m : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    amplitude l m*b^(l+1+2*m) ≤
      (amplitude l 0*b^(l+1))*((b^2/2)^m/(Nat.factorial m : ℝ)) := by
  calc
    _ ≤ (amplitude l 0/(2^m*(Nat.factorial m : ℝ)))*b^(l+1+2*m) :=
      mul_le_mul_of_nonneg_right (amplitude_le_majorant l m) (pow_nonneg hb _)
    _ = _ := by
      rw [pow_add,pow_mul,div_pow]
      field_simp
      ring

theorem index_growth (l m : ℕ) : (l+1+2*m : ℝ) ≤ (l+2)*2^m := by
  have hm : (m+1 : ℝ) ≤ 2^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      push_cast
      linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ l+2),mul_nonneg hl hm']

theorem derivative_power_majorant (l m : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    amplitude l m*(l+1+2*m)*b^(l+1+2*m) ≤
      (amplitude l 0*(l+2)*b^(l+1))*((b^2)^m/(Nat.factorial m : ℝ)) := by
  calc
    _ ≤ (amplitude l 0/(2^m*(Nat.factorial m : ℝ)))*((l+2)*2^m)*b^(l+1+2*m) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _)
      exact mul_le_mul (amplitude_le_majorant l m) (index_growth l m) (by positivity)
        (div_nonneg (amplitude_pos l 0).le (by positivity))
    _ = _ := by
      rw [pow_add,pow_mul]
      field_simp
      ring

end OQ14.RiccatiSeriesCoefficients

#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_pos
#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_zero_degree
#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_raising
#print axioms OQ14.RiccatiSeriesCoefficients.coeff_raising
#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_recurrence
#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_factorial_bound
#print axioms OQ14.RiccatiSeriesCoefficients.amplitude_le_majorant
#print axioms OQ14.RiccatiSeriesCoefficients.coeff_abs
#print axioms OQ14.RiccatiSeriesCoefficients.power_majorant
#print axioms OQ14.RiccatiSeriesCoefficients.index_growth
#print axioms OQ14.RiccatiSeriesCoefficients.derivative_power_majorant

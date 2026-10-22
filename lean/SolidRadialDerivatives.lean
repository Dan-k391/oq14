import SolidRadialSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Genuine all-order derivative series and bounds for the squared-radius regular factor. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SolidRadialDerivatives

open Complex OQ14.SolidRadialSeries OQ14.RiccatiSeriesCoefficients

def coefficientD (l : ℕ) : ℕ → ℕ → ℂ
  | 0 => coefficient l
  | j+1 => EntireFactorialSeries.shift (coefficientD l j)

def seriesD (l j : ℕ) : ℂ → ℂ := EntireFactorialSeries.sum (coefficientD l j)

theorem coefficientD_norm (l j m : ℕ) : ‖coefficientD l j m‖ ≤ amplitude l m := by
  induction j generalizing m with
  | zero => exact (coefficient_norm l m).le
  | succ j ih =>
    simp only [coefficientD,EntireFactorialSeries.shift,norm_mul,Complex.norm_natCast]
    have h := mul_le_mul_of_nonneg_right (ih (m+1)) (by positivity : 0 ≤ ((m+1 : ℕ) : ℝ))
    have hstep : amplitude l (m+1)*((m+1 : ℕ) : ℝ) ≤ amplitude l m := by
      simpa only [Nat.cast_add,Nat.cast_one,mul_comm] using amplitude_step_bound l m
    exact h.trans hstep

theorem coefficientD_bound (l j m : ℕ) :
    ‖coefficientD l j m‖ ≤ amplitude l 0/(2^m*(m.factorial : ℝ)) :=
  (coefficientD_norm l j m).trans (amplitude_le_majorant l m)

theorem seriesD_hasDerivAt (l j : ℕ) (t : ℂ) : HasDerivAt (seriesD l j) (seriesD l (j+1) t) t :=
  EntireFactorialSeries.sum_hasDerivAt (coefficientD l j) (amplitude l 0)
    (amplitude_pos l 0).le (coefficientD_bound l j) t

theorem seriesD_analyticAt (l j : ℕ) (t : ℂ) : AnalyticAt ℂ (seriesD l j) t :=
  EntireFactorialSeries.sum_analyticAt (coefficientD l j) (amplitude l 0)
    (amplitude_pos l 0).le (coefficientD_bound l j) t

theorem seriesD_contDiff (l j : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (seriesD l j) :=
  AnalyticOnNhd.contDiff (fun t _ => seriesD_analyticAt l j t)

theorem iteratedDeriv_F (l j : ℕ) : iteratedDeriv j (F l)=seriesD l j := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]; rfl
  | succ j ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext (fun t => (seriesD_hasDerivAt l j t).deriv)

theorem seriesD_norm_bound (l j : ℕ) (t : ℂ) :
    ‖seriesD l j t‖ ≤ amplitude l 0*Real.exp (‖t‖/2) := by
  have hs : HasSum (fun m : ℕ => (‖t‖/2)^m/(m.factorial : ℝ)) (Real.exp (‖t‖/2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (‖t‖/2)
  exact tsum_of_norm_bounded (hs.mul_left (amplitude l 0))
    (fun m => EntireFactorialSeries.term_bound (coefficientD l j) (amplitude l 0) ‖t‖
      (amplitude_pos l 0).le (norm_nonneg t) (coefficientD_bound l j) m t le_rfl)

theorem iteratedDeriv_norm_bound (l j : ℕ) (t : ℂ) :
    ‖iteratedDeriv j (F l) t‖ ≤ amplitude l 0*Real.exp (‖t‖/2) := by
  rw [iteratedDeriv_F]
  exact seriesD_norm_bound l j t

theorem coefficientD_factorial (l j m : ℕ) :
    coefficientD l j m = coefficient l (m+j)*(Nat.factorial (m+j) : ℂ)/(Nat.factorial m : ℂ) := by
  induction j generalizing m with
  | zero =>
    simp only [coefficientD,Nat.add_zero]
    have hf : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp [hf]
  | succ j ih =>
    simp only [coefficientD,EntireFactorialSeries.shift]
    have hf : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hm : (m : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have hfac : (Nat.factorial (m+1) : ℂ)=((m : ℂ)+1)*(Nat.factorial m : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      rfl
    rw [ih,show m+1+j=m+(j+1) by omega,hfac]
    push_cast
    field_simp [hf,hm]
    ring

theorem seriesD_zero (l j : ℕ) : seriesD l j 0=coefficient l j*(j.factorial : ℂ) := by
  unfold seriesD EntireFactorialSeries.sum
  rw [tsum_eq_single 0]
  · simp only [EntireFactorialSeries.term,pow_zero,mul_one,coefficientD_factorial,Nat.zero_add,
      Nat.factorial_zero,Nat.cast_one,div_one]
  · intro m hm
    simp only [EntireFactorialSeries.term,zero_pow hm,mul_zero]

theorem iteratedDeriv_zero (l j : ℕ) :
    iteratedDeriv j (F l) 0=(coeff l j : ℂ)*(j.factorial : ℂ) := by
  rw [iteratedDeriv_F,seriesD_zero]
  rfl

end OQ14.SolidRadialDerivatives

#print axioms OQ14.SolidRadialDerivatives.coefficientD_norm
#print axioms OQ14.SolidRadialDerivatives.coefficientD_bound
#print axioms OQ14.SolidRadialDerivatives.seriesD_hasDerivAt
#print axioms OQ14.SolidRadialDerivatives.seriesD_analyticAt
#print axioms OQ14.SolidRadialDerivatives.seriesD_contDiff
#print axioms OQ14.SolidRadialDerivatives.iteratedDeriv_F
#print axioms OQ14.SolidRadialDerivatives.seriesD_norm_bound
#print axioms OQ14.SolidRadialDerivatives.iteratedDeriv_norm_bound
#print axioms OQ14.SolidRadialDerivatives.coefficientD_factorial
#print axioms OQ14.SolidRadialDerivatives.seriesD_zero
#print axioms OQ14.SolidRadialDerivatives.iteratedDeriv_zero

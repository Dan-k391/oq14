import EntireFactorialSeries
import RiccatiGaussianBound

/-! Actual entire regular radial factors as functions of squared radius. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SolidRadialSeries

open Complex OQ14.RiccatiSeriesCoefficients

def coefficient (l m : ℕ) : ℂ := (coeff l m : ℂ)
def F (l : ℕ) : ℂ → ℂ := EntireFactorialSeries.sum (coefficient l)
def F1 (l : ℕ) : ℂ → ℂ := EntireFactorialSeries.sum (EntireFactorialSeries.shift (coefficient l))
def F2 (l : ℕ) : ℂ → ℂ := EntireFactorialSeries.sum (EntireFactorialSeries.shift (EntireFactorialSeries.shift (coefficient l)))

theorem coefficient_norm (l m : ℕ) : ‖coefficient l m‖ = amplitude l m := by
  simp only [coefficient,Complex.norm_real,Real.norm_eq_abs,coeff_abs]

theorem coefficient_bound (l m : ℕ) :
    ‖coefficient l m‖ ≤ amplitude l 0/(2^m*(m.factorial : ℝ)) := by
  rw [coefficient_norm]
  exact amplitude_le_majorant l m

theorem amplitude_step_bound (l m : ℕ) : (m+1 : ℝ)*amplitude l (m+1) ≤ amplitude l m := by
  have hr := amplitude_recurrence l m
  have hfac : 1 ≤ 2*(2*((l : ℝ)+m)+3) := by
    have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h := mul_le_mul_of_nonneg_right hfac
    (mul_nonneg (by positivity : 0 ≤ (m+1 : ℝ)) (amplitude_pos l (m+1)).le)
  calc
    _ ≤ 2*(2*((l : ℝ)+m)+3)*((m+1)*amplitude l (m+1)) := by simpa only [one_mul] using h
    _ = _ := by nlinarith [hr]

theorem shifted_coefficient_bound (l m : ℕ) :
    ‖EntireFactorialSeries.shift (coefficient l) m‖ ≤ amplitude l 0/(2^m*(m.factorial : ℝ)) := by
  simp only [EntireFactorialSeries.shift,norm_mul,Complex.norm_natCast,coefficient_norm]
  have h : amplitude l (m+1)*(m+1 : ℝ) ≤ amplitude l m := by
    simpa only [mul_comm] using amplitude_step_bound l m
  simpa only [Nat.cast_add,Nat.cast_one] using h.trans (amplitude_le_majorant l m)

theorem F_hasDerivAt (l : ℕ) (t : ℂ) : HasDerivAt (F l) (F1 l t) t :=
  EntireFactorialSeries.sum_hasDerivAt (coefficient l) (amplitude l 0) (amplitude_pos l 0).le
    (coefficient_bound l) t

theorem F1_hasDerivAt (l : ℕ) (t : ℂ) : HasDerivAt (F1 l) (F2 l t) t :=
  EntireFactorialSeries.sum_hasDerivAt (EntireFactorialSeries.shift (coefficient l))
    (amplitude l 0) (amplitude_pos l 0).le (shifted_coefficient_bound l) t

theorem F_analyticAt (l : ℕ) (t : ℂ) : AnalyticAt ℂ (F l) t :=
  EntireFactorialSeries.sum_analyticAt (coefficient l) (amplitude l 0) (amplitude_pos l 0).le
    (coefficient_bound l) t

theorem F1_analyticAt (l : ℕ) (t : ℂ) : AnalyticAt ℂ (F1 l) t :=
  EntireFactorialSeries.sum_analyticAt (EntireFactorialSeries.shift (coefficient l))
    (amplitude l 0) (amplitude_pos l 0).le (shifted_coefficient_bound l) t

theorem F_contDiff (l : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (F l) :=
  AnalyticOnNhd.contDiff (fun t _ => F_analyticAt l t)

theorem F_zero (l : ℕ) : F l 0 = (amplitude l 0 : ℂ) := by
  unfold F EntireFactorialSeries.sum
  rw [tsum_eq_single 0]
  · simp [EntireFactorialSeries.term,coefficient,coeff]
  · intro m hm
    simp only [EntireFactorialSeries.term,zero_pow hm,mul_zero]

theorem origin_factor (l : ℕ) (z : ℂ) : OQ14.RiccatiOriginSeries.origin l z = z^(l+1)*F l (z^2) := by
  unfold OQ14.RiccatiOriginSeries.origin F EntireFactorialSeries.sum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  simp only [OQ14.RiccatiOriginSeries.term,EntireFactorialSeries.term,coefficient,pow_add,pow_mul]
  ring

theorem coefficient_recurrence (l m : ℕ) :
    2*(m+1 : ℕ)*(2*(l+m : ℕ)+3)*coefficient l (m+1)+coefficient l m = 0 := by
  have hr := amplitude_recurrence l m
  have hreal : 2*(m+1 : ℝ)*(2*((l : ℝ)+m)+3)*coeff l (m+1)+coeff l m = 0 := by
    rw [coeff,coeff,pow_succ]
    linear_combination -((-1 : ℝ)^m)*hr
  dsimp only [coefficient]
  exact_mod_cast hreal

theorem normalized_ode (l : ℕ) (t : ℂ) :
    4*t*F2 l t+(4*l+6 : ℂ)*F1 l t+F l t = 0 := by
  let G : ℕ → ℂ := fun m => (4*l+6 : ℂ)*EntireFactorialSeries.term
      (EntireFactorialSeries.shift (coefficient l)) m t+EntireFactorialSeries.term (coefficient l) m t
  have h0 := EntireFactorialSeries.terms_summable (coefficient l) (amplitude l 0)
    (amplitude_pos l 0).le (coefficient_bound l) t
  have h1 := EntireFactorialSeries.terms_summable (EntireFactorialSeries.shift (coefficient l))
    (amplitude l 0) (amplitude_pos l 0).le (shifted_coefficient_bound l) t
  have hG : Summable G := (h1.mul_left (4*l+6 : ℂ)).add h0
  have hsum : (∑' m : ℕ, G m) = (4*l+6 : ℂ)*F1 l t+F l t := by
    rw [(h1.mul_left (4*l+6 : ℂ)).tsum_add h0,tsum_mul_left]
    rfl
  have hG0 : G 0=0 := by
    dsimp [G,EntireFactorialSeries.term,EntireFactorialSeries.shift]
    simp only [Nat.cast_zero,zero_add,pow_zero,mul_one,Nat.cast_one]
    convert coefficient_recurrence l 0 using 1
    push_cast
    ring
  have hGs : ∀ m : ℕ, G (m+1) = (-4*t)*EntireFactorialSeries.term
      (EntireFactorialSeries.shift (EntireFactorialSeries.shift (coefficient l))) m t := by
    intro m
    dsimp [G,EntireFactorialSeries.term,EntireFactorialSeries.shift]
    rw [show t^(m+1)=t^m*t from pow_succ t m]
    have hr := coefficient_recurrence l (m+1)
    push_cast at hr ⊢
    linear_combination (t^m*t)*hr
  calc
    _ = 4*t*F2 l t+((4*l+6 : ℂ)*F1 l t+F l t) := by ring
    _ = 4*t*F2 l t+∑' m : ℕ, G m := by rw [hsum]
    _ = 4*t*F2 l t+∑' m : ℕ, G (m+1) := by rw [hG.tsum_eq_zero_add,hG0,zero_add]
    _ = 4*t*F2 l t+(-4*t)*F2 l t := by rw [tsum_congr hGs,tsum_mul_left]; rfl
    _ = 0 := by ring

theorem deriv_F (l : ℕ) : deriv (F l)=F1 l := funext (fun t => (F_hasDerivAt l t).deriv)

theorem deriv_F1 (l : ℕ) : deriv (F1 l)=F2 l := funext (fun t => (F1_hasDerivAt l t).deriv)

theorem normalized_ode_deriv (l : ℕ) (t : ℂ) :
    4*t*deriv (deriv (F l)) t+(4*l+6 : ℂ)*deriv (F l) t+F l t = 0 := by
  rw [deriv_F,deriv_F1]
  exact normalized_ode l t

theorem F1_contDiff (l : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (F1 l) :=
  AnalyticOnNhd.contDiff (fun t _ => F1_analyticAt l t)

theorem normalized_away (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    F l (z^2)=OQ14.ModalAlgebra.psi l z/z^(l+1) := by
  have h := origin_factor l z
  rw [OQ14.RiccatiOriginSeries.origin_eq_psi l z hz] at h
  exact (eq_div_iff (pow_ne_zero _ hz)).mpr (by simpa only [mul_comm] using h.symm)

theorem regular_factor (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    (OQ14.HankelRealBasis.regular l r : ℂ)=(r : ℂ)^(l+1)*F l ((r : ℂ)^2) := by
  rw [OQ14.HankelRealBasis.regular_eq_psi,← OQ14.RiccatiOriginSeries.origin_eq_psi l (r : ℂ) (Complex.ofReal_ne_zero.mpr hr)]
  exact origin_factor l (r : ℂ)

theorem F_norm_bound (l : ℕ) (t : ℂ) : ‖F l t‖ ≤ amplitude l 0*Real.exp (‖t‖/2) := by
  have hs : HasSum (fun m : ℕ => (‖t‖/2)^m/(m.factorial : ℝ)) (Real.exp (‖t‖/2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (‖t‖/2)
  exact tsum_of_norm_bounded (hs.mul_left (amplitude l 0))
    (fun m => EntireFactorialSeries.term_bound (coefficient l) (amplitude l 0) ‖t‖
      (amplitude_pos l 0).le (norm_nonneg t) (coefficient_bound l) m t le_rfl)

theorem F1_norm_bound (l : ℕ) (t : ℂ) : ‖F1 l t‖ ≤ amplitude l 0*Real.exp (‖t‖/2) := by
  have hs : HasSum (fun m : ℕ => (‖t‖/2)^m/(m.factorial : ℝ)) (Real.exp (‖t‖/2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (‖t‖/2)
  exact tsum_of_norm_bounded (hs.mul_left (amplitude l 0))
    (fun m => EntireFactorialSeries.term_bound (EntireFactorialSeries.shift (coefficient l))
      (amplitude l 0) ‖t‖ (amplitude_pos l 0).le (norm_nonneg t) (shifted_coefficient_bound l) m t le_rfl)

end OQ14.SolidRadialSeries

#print axioms OQ14.SolidRadialSeries.coefficient_norm
#print axioms OQ14.SolidRadialSeries.coefficient_bound
#print axioms OQ14.SolidRadialSeries.amplitude_step_bound
#print axioms OQ14.SolidRadialSeries.shifted_coefficient_bound
#print axioms OQ14.SolidRadialSeries.F_hasDerivAt
#print axioms OQ14.SolidRadialSeries.F1_hasDerivAt
#print axioms OQ14.SolidRadialSeries.F_analyticAt
#print axioms OQ14.SolidRadialSeries.F1_analyticAt
#print axioms OQ14.SolidRadialSeries.F_contDiff
#print axioms OQ14.SolidRadialSeries.F_zero
#print axioms OQ14.SolidRadialSeries.origin_factor
#print axioms OQ14.SolidRadialSeries.coefficient_recurrence
#print axioms OQ14.SolidRadialSeries.normalized_ode
#print axioms OQ14.SolidRadialSeries.deriv_F
#print axioms OQ14.SolidRadialSeries.deriv_F1
#print axioms OQ14.SolidRadialSeries.normalized_ode_deriv
#print axioms OQ14.SolidRadialSeries.F1_contDiff
#print axioms OQ14.SolidRadialSeries.normalized_away
#print axioms OQ14.SolidRadialSeries.regular_factor
#print axioms OQ14.SolidRadialSeries.F_norm_bound
#print axioms OQ14.SolidRadialSeries.F1_norm_bound

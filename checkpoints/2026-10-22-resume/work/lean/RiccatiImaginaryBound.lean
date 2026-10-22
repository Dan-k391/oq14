import SolidRadialSeries
import RadialFullMajorant

/-! Actual noncancelling imaginary-axis regular waves and spatial normalization control. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.RiccatiImaginaryBound
open Complex OQ14.RiccatiSeriesCoefficients OQ14.SolidRadialSeries

theorem negative_term (l m : ℕ) (t : ℝ) :
    EntireFactorialSeries.term (coefficient l) m (-(t : ℂ))=(amplitude l m*t^m : ℝ) := by
  have h : coeff l m*(-t)^m=amplitude l m*t^m := by
    rw [coeff,neg_pow t m]
    calc
      (-1 : ℝ)^m*amplitude l m*((-1)^m*t^m)=
          ((-1 : ℝ)*(-1))^m*amplitude l m*t^m := by rw [mul_pow]; ring
      _ = _ := by simp
  dsimp only [EntireFactorialSeries.term,coefficient]
  exact_mod_cast h

theorem F_negative_re_lower (l : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    amplitude l 0 ≤ (F l (-(t : ℂ))).re := by
  have hs := EntireFactorialSeries.terms_summable (coefficient l) (amplitude l 0)
    (amplitude_pos l 0).le (coefficient_bound l) (-(t : ℂ))
  have hr := (Complex.hasSum_re hs.hasSum).summable
  have hn (m : ℕ) : 0 ≤ (EntireFactorialSeries.term (coefficient l) m (-(t : ℂ))).re := by
    rw [negative_term,ofReal_re]
    exact mul_nonneg (amplitude_pos l m).le (pow_nonneg ht _)
  have h := hr.le_tsum 0 (fun m _ => hn m)
  change amplitude l 0 ≤ (∑' m,EntireFactorialSeries.term (coefficient l) m (-(t : ℂ))).re
  rw [Complex.re_tsum hs]
  simpa only [negative_term,pow_zero,mul_one,ofReal_re] using h

theorem origin_imaginary_lower (l : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    amplitude l 0*b^(l+1) ≤ ‖RiccatiOriginSeries.origin l (I*(b : ℂ))‖ := by
  rw [origin_factor,norm_mul,norm_pow,norm_mul,norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hb,one_mul]
  have he : (I*(b : ℂ))^2= -((b^2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (b : ℂ)^2*Complex.I_sq
  rw [he]
  have h := (F_negative_re_lower l (b^2) (sq_nonneg b)).trans (Complex.re_le_norm _)
  nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hb (l+1))]

theorem gamma_amplitude_control (l : ℕ) (gs : List RadialStack.Layer) (R X b : ℝ)
    (hR : 0 < R) (hb : 0 ≤ b) :
    ‖RadialSource.gamma l gs R X hR‖*(amplitude l 0)^2*b^(2*(l+1)) ≤
      ‖RadialEntireReaction.component l 0 0 gs R X hR (I*(b : ℂ)) (I*(b : ℂ))‖ := by
  simp only [RadialEntireReaction.component,iteratedDeriv_zero,norm_mul]
  have h := origin_imaginary_lower l b hb
  have hh := mul_le_mul h h (mul_nonneg (amplitude_pos l 0).le (pow_nonneg hb _)) (norm_nonneg _)
  have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg (RadialSource.gamma l gs R X hR))
  convert hh' using 1 <;> ring


theorem gamma_weighted_amplitude_bound (l k : ℕ) {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hb : 1 ≤ b) (ht : Real.exp 1*b ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (hqp : ∀ g ∈ gs, g.q ≤ q) :
    (l+1 : ℝ)^k*‖RadialSource.gamma l gs R X (by linarith)‖*(amplitude l 0)^2*b^(2*l) ≤
      RadialFullMajorant.majorant q M d b k l := by
  have hRp : 0 < R := by linarith
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hlow := gamma_amplitude_control l gs R X b hRp hb0.le
  have hpow : b^(2*l) ≤ b^(2*(l+1)) := pow_le_pow_right₀ hb (by omega)
  have hprod := (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (norm_nonneg _) (sq_nonneg (amplitude l 0)))).trans hlow
  have hweighted := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (l+1 : ℝ)^k)
  have hz : ‖I*(b : ℂ)‖+((0 : ℕ) : ℝ) ≤ b := by
    simp only [norm_mul,norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb0.le,one_mul,Nat.cast_zero,add_zero,le_refl]
  have hh := RadialFullMajorant.component_weighted_bound l k 0 0 hc q M d b hq hM hR hb0 ht hX hd hp hqp
    (I*(b : ℂ)) (I*(b : ℂ)) hz hz
  apply le_trans _ hh
  convert hweighted using 1; ring

end OQ14.RiccatiImaginaryBound

#print axioms OQ14.RiccatiImaginaryBound.negative_term

#print axioms OQ14.RiccatiImaginaryBound.F_negative_re_lower

#print axioms OQ14.RiccatiImaginaryBound.origin_imaginary_lower

#print axioms OQ14.RiccatiImaginaryBound.gamma_amplitude_control

#print axioms OQ14.RiccatiImaginaryBound.gamma_weighted_amplitude_bound

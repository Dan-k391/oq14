import FiniteSphereReactionScale

/-! Actual parity gain amplification of derived small-sphere reaction errors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.ReactionGainError

theorem gain_bound (b a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    |(b/a)^2-1| ≤ (b^2+1)/a^2 := by
  have ha2 : a^2 ≤ 1 := by nlinarith
  calc
    |(b/a)^2-1| ≤ (b/a)^2+1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (b/a)]
    _ = (b^2+a^2)/a^2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right (add_le_add_left ha2 _) (sq_nonneg _)

theorem amplified_error (b a C : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (e : ℂ) (he : ‖e‖ ≤ C*a^3) :
    ‖(((b/a)^2-1 : ℝ) : ℂ)*e‖ ≤ (b^2+1)*C*a := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply (mul_le_mul (gain_bound b a ha ha1) he (norm_nonneg e)
    (div_nonneg (by positivity) (sq_nonneg a))).trans_eq
  field_simp
  ring

theorem inverse_gain_bound (b a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    |(b/a)⁻¹^2-1| ≤ 1+1/b^2 := by
  have ha2 : a^2 ≤ 1 := by nlinarith
  have he : (b/a)⁻¹^2 = a^2/b^2 := by simp only [inv_div, div_pow]
  calc
    |(b/a)⁻¹^2-1| ≤ (b/a)⁻¹^2+1 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg ((b/a)⁻¹)]
    _ ≤ 1+1/b^2 := by rw [he]; linarith [div_le_div_of_nonneg_right ha2 (sq_nonneg b)]

theorem amplified_inverse_error (b a C : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (e : ℂ) (he : ‖e‖ ≤ C*a^3) :
    ‖(((b/a)⁻¹^2-1 : ℝ) : ℂ)*e‖ ≤ (1+1/b^2)*C*a^3 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (inverse_gain_bound b a ha ha1) he (norm_nonneg e)
    (by positivity : 0 ≤ 1+1/b^2)).trans_eq (by ring)

theorem combined_error (b a C : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (e f : ℂ) (he : ‖e‖ ≤ C*a^3) (hf : ‖f‖ ≤ C*a^3) :
    ‖(((b/a)^2-1 : ℝ) : ℂ)*e+(((b/a)⁻¹^2-1 : ℝ) : ℂ)*f‖ ≤
      (b^2+2+1/b^2)*C*a := by
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg e).trans he) (pow_pos ha 3)
  have ha2 : a^2 ≤ 1 := by nlinarith
  have ha3 : a^3 ≤ a := by
    calc
      a^3 = a^2*a := by ring
      _ ≤ 1*a := mul_le_mul_of_nonneg_right ha2 ha.le
      _ = a := one_mul a
  apply (norm_add_le _ _).trans
  apply (add_le_add (amplified_error b a C ha ha1 e he)
    ((amplified_inverse_error b a C ha.le ha1 f hf).trans
      (mul_le_mul_of_nonneg_left ha3 (mul_nonneg (by positivity) hC)))).trans_eq
  ring

end OQ14.ReactionGainError

#print axioms OQ14.ReactionGainError.gain_bound
#print axioms OQ14.ReactionGainError.amplified_error
#print axioms OQ14.ReactionGainError.inverse_gain_bound
#print axioms OQ14.ReactionGainError.amplified_inverse_error
#print axioms OQ14.ReactionGainError.combined_error

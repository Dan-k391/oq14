import Packet06ComplexReciprocal

/-! Exact positive frequency placement and quality-factor ratio under dilation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06FrequencyPlacement

theorem positive_real_frequency (z : ℂ) (target : ℝ) (hz : 0 < z.re) (ht : 0 < target) :
    ∃ s : ℝ, 0 < s ∧ ((s : ℂ)*z).re = target ∧
      ((s : ℂ)*z).im = s*z.im ∧
      -((s : ℂ)*z).re / (2*((s : ℂ)*z).im) = -z.re / (2*z.im) := by
  refine ⟨target/z.re, div_pos ht hz, ?_, ?_, ?_⟩
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp
  · simp
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    have hs : target/z.re ≠ 0 := (div_pos ht hz).ne'
    by_cases hi : z.im = 0
    · simp [hi]
    · field_simp
      ring

end OQ14.Packet06FrequencyPlacement
#print axioms OQ14.Packet06FrequencyPlacement.positive_real_frequency

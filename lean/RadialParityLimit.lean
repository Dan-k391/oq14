import RadialPhaseLimit

/-! Exact parity values of the actual common quarter-wave source limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialParityLimit
open Set Filter Complex OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack
  OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
open scoped Topology

theorem backward_reference_pair (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (s : State) :
    RadialReference.solution q σ hq.ne' hσ.ne'
      (RadialReference.solution 1 1 one_ne_zero one_ne_zero s (-Real.pi/2))
      (-(Real.pi/(2*q))) = (((-σ/q : ℝ) : ℂ)*s.1,((-q/σ : ℝ) : ℂ)*s.2) := by
  have he : q*(Real.pi/(2*q))=Real.pi/2 := by field_simp; ring
  apply Prod.ext <;>
    simp [RadialReference.solution,RadialReference.matrix,act,mul_neg,he,neg_div,Real.cos_neg,Real.sin_neg]

theorem backward_reference_pairs (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (n : ℕ) (s : State) :
    RadialBackwardLimit.reference (pairs q σ hq hσ n) s =
      ((((-σ/q : ℝ)^n : ℝ) : ℂ)*s.1,(((-q/σ : ℝ)^n : ℝ) : ℂ)*s.2) := by
  induction n with
  | zero => simp [pairs,RadialBackwardLimit.reference]
  | succ n ih =>
    simp only [pairs,RadialBackwardLimit.reference,high,low]
    rw [show -(Real.pi/2) = -Real.pi/2 by ring,
      backward_reference_pair q σ hq hσ,ih]
    apply Prod.ext <;> simp only [pow_succ,Complex.ofReal_mul] <;> ring

theorem phase_even (j : ℕ) : phase (2*j) = (((-1 : ℝ)^j : ℝ) : ℂ)*(-I) := by
  simp [phase,pow_add,pow_mul]

theorem phase_odd (j : ℕ) : phase (2*j+1) = (((-1 : ℝ)^(j+1) : ℝ) : ℂ) := by
  rw [phase,show 2*j+1+1=2*(j+1) by omega,pow_mul]
  simp

theorem even_ratio (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    (limitingCoefficients (2*j) (pairs q σ hq hσ n)).1 /
      (limitingCoefficients (2*j) (pairs q σ hq hσ n)).2 =
        -I*(((q/σ)^(2*n) : ℝ) : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have hσC : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hs : ((-1 : ℝ)^j : ℂ) ≠ 0 := by simp
  rw [limitingCoefficients,backward_reference_pairs]
  simp only [act,inverse,phaseBasis,phase_even,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,I_re,I_im,
    mul_zero,zero_mul,mul_one,mul_neg,neg_zero,add_zero,zero_add,sub_zero,zero_sub,
    Complex.ofReal_neg,Complex.ofReal_zero,Complex.ofReal_mul]
  push_cast
  simp only [show 2*n=n*2 by omega,pow_mul,div_pow,neg_pow (q : ℂ) n,neg_pow (σ : ℂ) n]
  field_simp [hqC,hσC]
  ring

theorem odd_ratio (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    (limitingCoefficients (2*j+1) (pairs q σ hq hσ n)).1 /
      (limitingCoefficients (2*j+1) (pairs q σ hq hσ n)).2 =
        -I*(((σ/q)^(2*n) : ℝ) : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  have hσC : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
  have hs : ((-1 : ℝ)^(j+1) : ℂ) ≠ 0 := by simp
  rw [limitingCoefficients,backward_reference_pairs]
  simp only [act,inverse,phaseBasis,phase_odd,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,I_re,I_im,mul_zero,zero_mul,mul_one,
    add_zero,zero_add,sub_zero,Complex.ofReal_zero,Complex.ofReal_neg]
  push_cast
  simp only [show 2*n=n*2 by omega,pow_mul,div_pow,neg_pow (q : ℂ) n,neg_pow (σ : ℂ) n]
  field_simp [hqC,hσC]
  ring_nf
  simp [Complex.I_sq]

theorem actual_gamma_even_limit (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    Tendsto (fun k : ℕ => RadialSource.gamma (2*j)
      (layers (pairs q σ hq hσ n) (radius k) (radius_pos k)) (radius k)
      (radius k+width (pairs q σ hq hσ n)) (radius_pos k)) atTop
      (𝓝 (-I*(((q/σ)^(2*n) : ℝ) : ℂ))) := by
  simpa only [even_ratio j n q σ hq hσ] using actual_gamma_limit (2*j) (pairs q σ hq hσ n)

theorem actual_gamma_odd_limit (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    Tendsto (fun k : ℕ => RadialSource.gamma (2*j+1)
      (layers (pairs q σ hq hσ n) (radius k) (radius_pos k)) (radius k)
      (radius k+width (pairs q σ hq hσ n)) (radius_pos k)) atTop
      (𝓝 (-I*(((σ/q)^(2*n) : ℝ) : ℂ))) := by
  simpa only [odd_ratio j n q σ hq hσ] using actual_gamma_limit (2*j+1) (pairs q σ hq hσ n)

end OQ14.RadialParityLimit

#print axioms OQ14.RadialParityLimit.backward_reference_pair
#print axioms OQ14.RadialParityLimit.backward_reference_pairs
#print axioms OQ14.RadialParityLimit.phase_even
#print axioms OQ14.RadialParityLimit.phase_odd
#print axioms OQ14.RadialParityLimit.even_ratio
#print axioms OQ14.RadialParityLimit.odd_ratio
#print axioms OQ14.RadialParityLimit.actual_gamma_even_limit
#print axioms OQ14.RadialParityLimit.actual_gamma_odd_limit

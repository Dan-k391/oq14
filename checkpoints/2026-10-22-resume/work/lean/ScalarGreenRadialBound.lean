import ScalarGreenNormalization
import HankelCoefficientBounds
import RiccatiCompactDerivatives

/-! Actual factorial cancellation and geometric off-diagonal Green radial bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenRadialBound
open Complex OQ14.RiccatiSeriesCoefficients OQ14.HankelCoefficientBounds

theorem amplitude_leading_product (l : ℕ) :
    amplitude l 0*coefficient l l=1/(2*(l : ℝ)+1) := by
  simp only [amplitude,coefficient,Nat.add_zero,Nat.sub_self,Nat.factorial_zero,Nat.cast_one,
    one_mul,mul_one,show l+l=2*l by omega]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

def radialFactor (l : ℕ) (k r s : ℝ) : ℂ :=
  I/(k : ℂ)*RiccatiOriginSeries.origin l ((k*r : ℝ) : ℂ)*ModalAlgebra.xi l ((k*s : ℝ) : ℂ)/
    ((r : ℂ)*(s : ℂ))

theorem radialFactor_bound (l : ℕ) (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) :
    ‖radialFactor l k r s‖ ≤
      Real.exp ((k*r)^2/2+k*s)/(s*(2*(l : ℝ)+1))*(r/s)^l := by
  have hkr := mul_pos hk hr
  have hks := mul_pos hk hs
  have ho := RiccatiCompactDerivatives.origin_norm_bound l (k*r) hkr.le ((k*r : ℝ) : ℂ)
    (by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hkr,le_refl])
  have hx := xi_exponential_bound l (k*s) hks
  have hA := (amplitude_pos l 0).le
  have hp := amplitude_leading_product l
  have hk0 := hk.ne'
  have hr0 := hr.ne'
  have hs0 := hs.ne'
  have hn : 0 < 2*(l : ℝ)+1 := by positivity
  simp only [radialFactor,norm_div,norm_mul,norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_pos hr,abs_of_pos hs]
  calc
    _ ≤ (1/k*(amplitude l 0*(k*r)^(l+1)*Real.exp ((k*r)^2/2)))*
        (coefficient l l/(k*s)^l*Real.exp (k*s))/(r*s) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hr hs).le
      exact mul_le_mul (mul_le_mul_of_nonneg_left ho (by positivity)) hx (norm_nonneg _)
        (by positivity : 0 ≤ 1/k*(amplitude l 0*(k*r)^(l+1)*Real.exp ((k*r)^2/2)))
    _ = _ := by
      rw [Real.exp_add]
      rw [show (k*r)^(l+1)=(k*r)^l*(k*r) from pow_succ _ _]
      simp only [mul_pow,div_pow]
      have hprod : amplitude l 0*coefficient l l*(2*(l : ℝ)+1)=1 :=
        (eq_div_iff hn.ne').mp hp
      field_simp [hk0,hr0,hs0,hn.ne']
      linear_combination (k*k^l*r*r^l*s*s^l*Real.exp (k^2*r^2/2)*Real.exp (k*s))*hprod

end OQ14.ScalarGreenRadialBound

#print axioms OQ14.ScalarGreenRadialBound.amplitude_leading_product

#print axioms OQ14.ScalarGreenRadialBound.radialFactor_bound

import ComplexMagneticLocal
import L1KernelOperator
import L2Parametric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticAnalytic
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.ComplexGreenKernel
open scoped Topology

def gradientDifference (z : ℂ) (x : Space) (j : Fin 3) : ℂ :=
  phiGradient z x j - phiGradient 0 x j

def gradientDerivative (z : ℂ) (x : Space) (j : Fin 3) : ℂ :=
  -z * exp (I*z*‖x‖) * ((x j / ‖x‖ : ℝ) : ℂ) / (4*Real.pi)

theorem gradient_hasDerivAt (z : ℂ) (x : Space) (j : Fin 3) :
    HasDerivAt (fun w => gradientDifference w x j) (gradientDerivative z x j) z := by
  by_cases hx : x = 0
  · subst x
    simpa [gradientDifference, gradientDerivative, phiGradient, radialD] using hasDerivAt_const z (0 : ℂ)
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  unfold gradientDifference gradientDerivative phiGradient radialD
  have h := (((hasDerivAt_const z I).mul (hasDerivAt_id z)).mul_const (‖x‖ : ℂ)).cexp
  have hm := (((hasDerivAt_const z I).mul (hasDerivAt_id z)).div_const (‖x‖ : ℂ)).sub_const (1 / (‖x‖ : ℂ)^2)
  have hh := ((h.mul hm).mul_const (((x j / ‖x‖ : ℝ) : ℂ))).div_const (4*Real.pi)
  have hh := hh.sub_const (exp (I*0*‖x‖) * (I*0 / (‖x‖ : ℂ) - 1/(‖x‖ : ℂ)^2) *
    (((x j / ‖x‖ : ℝ) : ℂ)) / (4*Real.pi))
  convert hh using 1
  simp only [id_eq, zero_mul, add_zero, mul_one]
  field_simp [hr, ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf
  simp [I_sq]
  field_simp [hr, ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

theorem derivative_bound (z : ℂ) (K R : ℝ) (hK : ‖z‖ ≤ K)
    (x : Space) (hx : ‖x‖ ≤ R) (j : Fin 3) :
    ‖gradientDerivative z x j‖ ≤ (4*Real.pi)⁻¹ * K * Real.exp (K*R) := by
  have hK0 : 0 ≤ K := (norm_nonneg z).trans hK
  have he : ‖exp (I*z*‖x‖)‖ ≤ Real.exp (K*R) := by
    apply (ComplexDynamicKernel.exp_norm_bound _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact mul_le_mul hK hx (norm_nonneg _) hK0
  have hu : ‖((x j / ‖x‖ : ℝ) : ℂ)‖ ≤ 1 := by
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm]
      exact (div_le_one hr).mpr (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
  have hp : 0 < 4 * Real.pi := by positivity
  unfold gradientDerivative
  simp only [norm_div, norm_mul, norm_neg]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (K * Real.exp (K*R) * 1) / (4*Real.pi) := by
      apply div_le_div_of_nonneg_right _ hp.le
      have hu' : |x j / ‖x‖| ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
      exact mul_le_mul (mul_le_mul hK he (norm_nonneg _) hK0) hu' (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem difference_bound (z : ℂ) (R : ℝ) (x : Space) (hx : ‖x‖ ≤ R) (j : Fin 3) :
    ‖gradientDifference z x j‖ ≤ ((4*Real.pi)⁻¹ * (‖z‖+1) * Real.exp ((‖z‖+1)*R)) * ‖z‖ := by
  let K := ‖z‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hz : z ∈ ball (0 : ℂ) K := by simp only [mem_ball, dist_zero_right]; dsimp [K]; linarith
  have h0 : (0 : ℂ) ∈ ball 0 K := by simp [hK]
  have hh := (convex_ball (0 : ℂ) K).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (gradient_hasDerivAt w x j).hasDerivWithinAt)
    (fun w hw => derivative_bound w K R (by
      have h := hw
      simp only [mem_ball, dist_zero_right] at h
      exact h.le) x hx j) h0 hz
  have hd0 : gradientDifference 0 x j = 0 := by simp [gradientDifference]
  simpa only [hd0, sub_zero, K] using hh

def kernel (z : ℂ) (R : ℝ) (j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => gradientDifference z x j)

def derivativeKernel (z : ℂ) (R : ℝ) (j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => gradientDerivative z x j)

theorem derivative_measurable (z : ℂ) (j : Fin 3) : Measurable (fun x => gradientDerivative z x j) := by
  unfold gradientDerivative
  fun_prop

theorem kernel_memLp (z : ℂ) (R : ℝ) (j : Fin 3) : MemLp (kernel z R j) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  apply MemLp.of_bound ((ComplexMagneticLocal.gradient_measurable z j).sub
    (ComplexMagneticLocal.gradient_measurable 0 j)).aestronglyMeasurable
    (((4*Real.pi)⁻¹ * (‖z‖+1) * Real.exp ((‖z‖+1)*R)) * ‖z‖)
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact difference_bound z R x (by simpa only [mem_closedBall, dist_zero_right] using hx) j

theorem derivative_memLp (z : ℂ) (R : ℝ) (j : Fin 3) : MemLp (derivativeKernel z R j) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  apply MemLp.of_bound (derivative_measurable z j).aestronglyMeasurable
    ((4*Real.pi)⁻¹ * ‖z‖ * Real.exp (‖z‖*R))
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact derivative_bound z ‖z‖ R le_rfl x (by simpa only [mem_closedBall, dist_zero_right] using hx) j

def kernelL2 (z : ℂ) (R : ℝ) (j : Fin 3) : Lp ℂ 2 (volume : Measure Space) :=
  (kernel_memLp z R j).toLp (kernel z R j)

def derivativeL2 (z : ℂ) (R : ℝ) (j : Fin 3) : Lp ℂ 2 (volume : Measure Space) :=
  (derivative_memLp z R j).toLp (derivativeKernel z R j)

theorem kernel_hasDerivAt (z : ℂ) (R : ℝ) (j : Fin 3) :
    HasDerivAt (fun w => kernelL2 w R j) (derivativeL2 z R j) z := by
  let K := ‖z‖+1
  let C := (4*Real.pi)⁻¹ * K * Real.exp (K*R)
  let b : Space → ℝ := (closedBall 0 R).indicator (fun _ => C)
  have hb : MemLp b 2 (volume : Measure Space) := by
    apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
    exact memLp_const C
  have hd : ∀ x w, HasDerivAt (fun q => kernel q R j x) (derivativeKernel w R j x) w := by
    intro x w
    by_cases hx : x ∈ closedBall (0 : Space) R
    · simpa only [kernel, derivativeKernel, indicator_of_mem hx] using gradient_hasDerivAt w x j
    · simpa only [kernel, derivativeKernel, indicator_of_not_mem hx] using hasDerivAt_const w (0 : ℂ)
  apply L2Parametric.hasDerivAt_toLp (fun w => kernel w R j) (fun w => derivativeKernel w R j)
    (fun w => kernel_memLp w R j) z (derivative_memLp z R j) hd b hb
  intro x w hw
  have hw1 : ‖w-z‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hwK : ‖w‖ ≤ K := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    dsimp [K]
    linarith
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simpa only [derivativeKernel, b, C, indicator_of_mem hx] using
      derivative_bound w K R hwK x (by simpa only [mem_closedBall, dist_zero_right] using hx) j
  · simp only [derivativeKernel, b, indicator_of_not_mem hx, norm_zero, le_refl]

theorem kernel_differentiable (R : ℝ) (j : Fin 3) :
    Differentiable ℂ (fun z => kernelL2 z R j) :=
  fun z => (kernel_hasDerivAt z R j).differentiableAt

#print axioms OQ14.ComplexMagneticAnalytic.kernel_differentiable
#print axioms OQ14.ComplexMagneticAnalytic.difference_bound
#print axioms OQ14.ComplexMagneticAnalytic.derivative_bound
#print axioms OQ14.ComplexMagneticAnalytic.gradient_hasDerivAt
end OQ14.ComplexMagneticAnalytic
















import ComplexDynamicKernel
import L2Parametric
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Banach L2 analyticity of the actual truncated complex remainder -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ComplexKernelAnalytic

open MeasureTheory Metric OQ14.Maxwell OQ14.DyadicKernel

def transverseD (z : ℂ) : ℂ := -Complex.exp z * z * (z + 1)
def radialD (z : ℂ) : ℂ := Complex.exp z * z * (z - 1)

theorem transverse_hasDerivAt (z : ℂ) :
    HasDerivAt transverseNumerator (transverseD z) z := by
  have hi := hasDerivAt_id z
  have he := Complex.hasDerivAt_exp z
  convert (he.mul (((hi.pow 2).neg.add hi).sub_const 1)).add_const 1 using 1
  dsimp [transverseNumerator, transverseD]
  ring

theorem radial_hasDerivAt (z : ℂ) :
    HasDerivAt radialNumerator (radialD z) z := by
  have hi := hasDerivAt_id z
  have he := Complex.hasDerivAt_exp z
  convert (he.mul (((hi.pow 2).sub (hi.const_mul 3)).add_const 3)).sub_const 3 using 1
  dsimp [radialNumerator, radialD]
  ring

theorem transverseD_bound (z : ℂ) :
    ‖transverseD z‖ ≤ Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1) := by
  unfold transverseD
  simp only [norm_mul, norm_neg]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (ComplexDynamicKernel.exp_norm_bound z) (norm_nonneg _))
    ((norm_add_le z 1).trans_eq (by rw [norm_one])) (norm_nonneg _) (by positivity)

theorem radialD_bound (z : ℂ) :
    ‖radialD z‖ ≤ Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1) := by
  unfold radialD
  simp only [norm_mul]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (ComplexDynamicKernel.exp_norm_bound z) (norm_nonneg _))
    ((norm_sub_le z 1).trans_eq (by rw [norm_one])) (norm_nonneg _) (by positivity)

def parameterDerivative (k : ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  ((transverseD (Complex.I * k * ‖x‖) * (if i = j then 1 else 0) +
    radialD (Complex.I * k * ‖x‖) * ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2)) *
      (Complex.I * ‖x‖)) / (4 * Real.pi * (‖x‖ : ℂ)^3)

theorem remainder_hasDerivAt (k : ℂ) (x : Space) (i j : Fin 3) :
    HasDerivAt (fun w => ComplexDynamicKernel.remainder w x i j)
      (parameterDerivative k x i j) k := by
  by_cases hx : x = 0
  · subst x
    simpa only [ComplexDynamicKernel.remainder_zero, parameterDerivative, norm_zero,
      Complex.ofReal_zero, mul_zero, zero_mul, zero_pow (by decide : 3 ≠ 0), div_zero] using
      hasDerivAt_const k (0 : ℂ)
  have hfun : (fun w => ComplexDynamicKernel.remainder w x i j) = fun w =>
      (transverseNumerator (Complex.I * w * ‖x‖) * (if i = j then 1 else 0) +
        radialNumerator (Complex.I * w * ‖x‖) *
          ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2)) /
            (4 * Real.pi * (‖x‖ : ℂ)^3) := by
    funext w
    rw [ComplexDynamicKernel.remainder_formula w x hx]
    ring
  rw [hfun]
  have hz : HasDerivAt (fun w : ℂ => Complex.I * w * ‖x‖) (Complex.I * ‖x‖) k := by
    convert ((hasDerivAt_id k).const_mul Complex.I).mul_const (‖x‖ : ℂ) using 1
    ring
  convert (((transverse_hasDerivAt _).comp k hz).mul_const (if i = j then 1 else 0) |>.add
    (((radial_hasDerivAt _).comp k hz).mul_const
      ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2))).div_const
        (4 * Real.pi * (‖x‖ : ℂ)^3) using 1
  dsimp [parameterDerivative]
  ring

theorem parameterDerivative_measurable (k : ℂ) (i j : Fin 3) :
    Measurable (fun x : Space => parameterDerivative k x i j) := by
  unfold parameterDerivative transverseD radialD
  fun_prop

theorem parameterDerivative_zero (k : ℂ) (i j : Fin 3) :
    parameterDerivative k 0 i j = 0 := by simp [parameterDerivative]

theorem parameterDerivative_bound (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    ‖parameterDerivative k x i j‖ ≤
      2 * Real.exp (‖k‖ * ‖x‖) * ‖k‖ * (‖k‖ * ‖x‖ + 1) / (4 * Real.pi * ‖x‖) := by
  let z : ℂ := Complex.I * k * ‖x‖
  have hn : ‖z‖ = ‖k‖ * ‖x‖ := by simp [z, norm_mul]
  have ht := transverseD_bound z
  have hr := radialD_bound z
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hc := normalized_coordinate_product_bound x hx i j
  have hnum : ‖transverseD z * (if i = j then 1 else 0) +
      radialD z * ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2)‖ ≤
      2 * Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1) := by
    calc
      _ ≤ ‖transverseD z‖ * ‖(if i = j then 1 else 0 : ℂ)‖ +
          ‖radialD z‖ * ‖(x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2‖ := by
        exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1)) * 1 +
          (Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1)) * 1 :=
        add_le_add (mul_le_mul ht hd (norm_nonneg _) (by positivity))
          (mul_le_mul hr hc (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hden : ‖(4 * Real.pi * (‖x‖ : ℂ)^3 : ℂ)‖ = 4 * Real.pi * ‖x‖^3 := by
    simp [norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  change ‖(_ * (Complex.I * ‖x‖)) / (4 * Real.pi * (‖x‖ : ℂ)^3)‖ ≤ _
  rw [norm_div, norm_mul, hden]
  have hi : ‖(Complex.I * ‖x‖ : ℂ)‖ = ‖x‖ := by simp [norm_mul]
  rw [hi]
  calc
    _ ≤ (2 * Real.exp ‖z‖ * ‖z‖ * (‖z‖ + 1)) * ‖x‖ /
        (4 * Real.pi * ‖x‖^3) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnum (norm_nonneg _)) (by positivity)
    _ = _ := by
      rw [hn]
      field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero]
      ring

def derivativeBound (K R : ℝ) : ℝ :=
  2 * Real.exp (K * R) * K * (K * R + 1) / (4 * Real.pi)

theorem parameterDerivative_bound_ball (k : ℂ) (K R : ℝ)
    (hk : ‖k‖ ≤ K) (_hR : 0 ≤ R) (x : Space) (hxR : ‖x‖ ≤ R) (i j : Fin 3) :
    ‖parameterDerivative k x i j‖ ≤ derivativeBound K R * ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [parameterDerivative_zero]
  have hK : 0 ≤ K := (norm_nonneg k).trans hk
  have hKR : ‖k‖ * ‖x‖ ≤ K * R := mul_le_mul hk hxR (norm_nonneg _) hK
  have hh : 2 * Real.exp (‖k‖ * ‖x‖) * ‖k‖ * (‖k‖ * ‖x‖ + 1) ≤
      2 * Real.exp (K * R) * K * (K * R + 1) := by gcongr
  apply (parameterDerivative_bound k x hx i j).trans
  have hb := div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 4 * Real.pi * ‖x‖)
  convert hb using 1
  dsimp [derivativeBound]
  field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero]

def kernel (k : ℂ) (R : ℝ) (i j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => ComplexDynamicKernel.remainder k x i j)

def derivativeKernel (k : ℂ) (R : ℝ) (i j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => parameterDerivative k x i j)

theorem kernel_memLp (k : ℂ) (R : ℝ) (i j : Fin 3) : MemLp (kernel k R i j) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    (ComplexDynamicKernel.remainder_memLp_two_ball k R i j)

theorem inverse_norm_memLp (R : ℝ) :
    MemLp (fun x : Space => ‖x‖⁻¹) 2 (volume.restrict (closedBall 0 R)) := by
  have hm : Measurable (fun x : Space => ‖x‖⁻¹) := continuous_norm.measurable.inv
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using KernelIntegrability.inverse_norm_sq_integrable_ball R

theorem derivativeKernel_memLp (k : ℂ) (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    MemLp (derivativeKernel k R i j) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
  apply (inverse_norm_memLp R).of_le_mul
    (parameterDerivative_measurable k i j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  simpa only [Real.norm_eq_abs, abs_inv, abs_norm] using
    parameterDerivative_bound_ball k ‖k‖ R le_rfl hR x
      (by simpa only [mem_closedBall, dist_zero_right] using hx) i j

def kernelL2 (k : ℂ) (R : ℝ) (i j : Fin 3) : Lp ℂ 2 (volume : Measure Space) :=
  (kernel_memLp k R i j).toLp (kernel k R i j)

def derivativeKernelL2 (k : ℂ) (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    Lp ℂ 2 (volume : Measure Space) :=
  (derivativeKernel_memLp k R hR i j).toLp (derivativeKernel k R i j)

theorem kernelL2_ae (k : ℂ) (R : ℝ) (i j : Fin 3) :
    (kernelL2 k R i j : Space → ℂ) =ᵐ[volume] kernel k R i j :=
  (kernel_memLp k R i j).coeFn_toLp

theorem kernelL2_supported (k : ℂ) (R : ℝ) (i j : Fin 3) :
    ∀ᵐ x : Space, x ∉ closedBall (0 : Space) R → kernelL2 k R i j x = 0 := by
  filter_upwards [kernelL2_ae k R i j] with x hx hn
  rw [hx]
  exact Set.indicator_of_not_mem hn _

theorem kernel_ofReal (k R : ℝ) (i j : Fin 3) :
    kernel (k : ℂ) R i j =
      (closedBall (0 : Space) R).indicator (fun x => DyadicKernel.remainder k x i j) := rfl

theorem kernel_hasDerivAt (k : ℂ) (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    HasDerivAt (fun w => kernelL2 w R i j) (derivativeKernelL2 k R hR i j) k := by
  let K : ℝ := ‖k‖ + 1
  let b : Space → ℝ := fun x => derivativeBound K R *
    (closedBall (0 : Space) R).indicator (fun y => ‖y‖⁻¹) x
  have hb : MemLp b 2 (volume : Measure Space) :=
    ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr (inverse_norm_memLp R)).const_mul _
  have hd : ∀ x w, HasDerivAt (fun z => kernel z R i j x) (derivativeKernel w R i j x) w := by
    intro x w
    by_cases hx : x ∈ closedBall (0 : Space) R
    · simpa only [kernel, derivativeKernel, Set.indicator_of_mem hx] using
        remainder_hasDerivAt w x i j
    · simpa only [kernel, derivativeKernel, Set.indicator_of_not_mem hx] using
        hasDerivAt_const w (0 : ℂ)
  apply L2Parametric.hasDerivAt_toLp (fun w => kernel w R i j)
    (fun w => derivativeKernel w R i j) (fun w => kernel_memLp w R i j) k
    (derivativeKernel_memLp k R hR i j) hd b hb
  intro x w hw
  have hw1 : ‖w-k‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hwK : ‖w‖ ≤ K := by
    have ht := norm_add_le (w-k) k
    rw [sub_add_cancel] at ht
    dsimp [K]
    linarith
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simpa only [derivativeKernel, b, Set.indicator_of_mem hx] using
      parameterDerivative_bound_ball w K R hwK hR x
        (by simpa only [mem_closedBall, dist_zero_right] using hx) i j
  · simp only [derivativeKernel, b, Set.indicator_of_not_mem hx, norm_zero, mul_zero, le_refl]

theorem kernel_differentiable (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    Differentiable ℂ (fun k => kernelL2 k R i j) :=
  fun k => (kernel_hasDerivAt k R hR i j).differentiableAt

theorem kernel_analyticAt (k : ℂ) (R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    AnalyticAt ℂ (fun w => kernelL2 w R i j) k :=
  (kernel_differentiable R hR i j).analyticAt k

end OQ14.ComplexKernelAnalytic

#print axioms OQ14.ComplexKernelAnalytic.transverse_hasDerivAt
#print axioms OQ14.ComplexKernelAnalytic.radial_hasDerivAt
#print axioms OQ14.ComplexKernelAnalytic.transverseD_bound
#print axioms OQ14.ComplexKernelAnalytic.radialD_bound
#print axioms OQ14.ComplexKernelAnalytic.remainder_hasDerivAt
#print axioms OQ14.ComplexKernelAnalytic.parameterDerivative_measurable
#print axioms OQ14.ComplexKernelAnalytic.parameterDerivative_zero
#print axioms OQ14.ComplexKernelAnalytic.parameterDerivative_bound
#print axioms OQ14.ComplexKernelAnalytic.parameterDerivative_bound_ball
#print axioms OQ14.ComplexKernelAnalytic.kernel_memLp
#print axioms OQ14.ComplexKernelAnalytic.inverse_norm_memLp
#print axioms OQ14.ComplexKernelAnalytic.derivativeKernel_memLp
#print axioms OQ14.ComplexKernelAnalytic.kernelL2_ae
#print axioms OQ14.ComplexKernelAnalytic.kernelL2_supported
#print axioms OQ14.ComplexKernelAnalytic.kernel_ofReal
#print axioms OQ14.ComplexKernelAnalytic.kernel_hasDerivAt
#print axioms OQ14.ComplexKernelAnalytic.kernel_differentiable
#print axioms OQ14.ComplexKernelAnalytic.kernel_analyticAt

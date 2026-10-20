import ComplexGreenKernel
import DynamicIntegrability

/-! # Complex-frequency dynamic Maxwell kernel

The dyadic uses the actual Hessian of the physical complex-frequency scalar
kernel. The static singularity cancels to a locally L1 and L2 remainder.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace OQ14.ComplexDynamicKernel

open MeasureTheory Metric OQ14.Maxwell OQ14.ComplexGreenKernel OQ14.DyadicKernel

def dyadic (k : ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  k^2 * phi k x * (if i = j then 1 else 0) + phiHessian k x i j

def remainder (k : ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  dyadic k x i j - phiHessian 0 x i j

theorem dyadic_actual_hessian (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dyadic k x i j = k^2 * phi k x * (if i = j then 1 else 0) +
      dcoord (fun y => dcoord (phi k) y j) x i := by
  rw [phi_second_partial k x hx]
  rfl

theorem remainder_formula (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    remainder k x i j =
      (transverseNumerator (Complex.I * k * ‖x‖) * (if i = j then 1 else 0) +
        radialNumerator (Complex.I * k * ‖x‖) * (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2) /
          (4 * Real.pi * (‖x‖ : ℂ)^3) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [remainder, dyadic, phi, phiHessian, radialDD, radialD, radial,
    transverseNumerator, radialNumerator, Complex.ofReal_zero,
    mul_zero, zero_mul, Complex.exp_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, zero_sub, zero_add, one_mul]
  generalize hrr : (‖x‖ : ℂ) = r at hr ⊢
  generalize hpp : (Real.pi : ℂ) = p at hp ⊢
  split_ifs <;> field_simp (maxDischargeDepth := 100) [hr, hp]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

theorem dyadic_ofReal (k : ℝ) (x : Space) (i j : Fin 3) :
    dyadic (k : ℂ) x i j = DyadicKernel.dyadic k x i j := rfl

theorem remainder_ofReal (k : ℝ) (x : Space) (i j : Fin 3) :
    remainder (k : ℂ) x i j = DyadicKernel.remainder k x i j := rfl

theorem exp_norm_bound (z : ℂ) : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (RCLike.re_le_norm z)

theorem transverse_bound (z : ℂ) :
    ‖transverseNumerator z‖ ≤ 4 * Real.exp ‖z‖ * ‖z‖^2 := by
  have he := exp_norm_bound z
  have he1 : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
  have he0 := (Real.exp_pos ‖z‖).le
  by_cases hz : ‖z‖ ≤ 1
  · rw [transverseNumerator_cancel]
    calc
      _ ≤ ‖-Complex.exp z * z^2‖ + ‖(Complex.exp z - 1) * z‖ +
          ‖Complex.exp z - 1 - z‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ Real.exp ‖z‖ * ‖z‖^2 + (2 * ‖z‖) * ‖z‖ + ‖z‖^2 := by
        simp only [norm_mul, norm_neg, norm_pow]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right he (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (exp_sub_one_bound z hz) (norm_nonneg _)))
          (Complex.norm_exp_sub_one_sub_id_le hz)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)]
  · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
    have hpoly : ‖-z^2 + z - 1‖ ≤ ‖z‖^2 + ‖z‖ + 1 := by
      calc
        _ ≤ ‖-z^2 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ (‖-z^2‖ + ‖z‖) + 1 := by
          rw [norm_one]
          exact add_le_add_right (norm_add_le (-z^2) z) 1
        _ = _ := by simp
    have htri : ‖transverseNumerator z‖ ≤
        ‖Complex.exp z‖ * ‖-z^2 + z - 1‖ + 1 := by
      calc
        _ ≤ ‖Complex.exp z * (-z^2 + z - 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_one]
    have hmul := mul_le_mul he hpoly (norm_nonneg _) he0
    have hsq : ‖z‖ ≤ ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    have hsq1 : 1 ≤ ‖z‖^2 := hz1.trans hsq
    nlinarith [mul_le_mul_of_nonneg_left hsq he0,
      mul_le_mul_of_nonneg_left hsq1 he0]

theorem radial_bound (z : ℂ) :
    ‖radialNumerator z‖ ≤ 10 * Real.exp ‖z‖ * ‖z‖^2 := by
  have he := exp_norm_bound z
  have he1 : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
  have he0 := (Real.exp_pos ‖z‖).le
  by_cases hz : ‖z‖ ≤ 1
  · rw [radialNumerator_cancel]
    calc
      _ ≤ ‖Complex.exp z * z^2‖ + ‖3 * (Complex.exp z - 1) * z‖ +
          ‖3 * (Complex.exp z - 1 - z)‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ ≤ Real.exp ‖z‖ * ‖z‖^2 + (3 * (2 * ‖z‖)) * ‖z‖ + 3 * ‖z‖^2 := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat]
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right he (sq_nonneg _))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (exp_sub_one_bound z hz) (by norm_num))
            (norm_nonneg _)))
          (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hz) (by norm_num))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)]
  · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
    have hpoly : ‖z^2 - 3*z + 3‖ ≤ ‖z‖^2 + 3*‖z‖ + 3 := by
      calc
        _ ≤ ‖z^2 - 3*z‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
        _ ≤ (‖z^2‖ + ‖3*z‖) + 3 := by
          rw [Complex.norm_ofNat]
          exact add_le_add_right (norm_sub_le (z^2) (3*z)) 3
        _ = _ := by simp [norm_mul]
    have htri : ‖radialNumerator z‖ ≤
        ‖Complex.exp z‖ * ‖z^2 - 3*z + 3‖ + 3 := by
      calc
        _ ≤ ‖Complex.exp z * (z^2 - 3*z + 3)‖ + ‖(3 : ℂ)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, Complex.norm_ofNat]
    have hmul := mul_le_mul he hpoly (norm_nonneg _) he0
    have hsq : ‖z‖ ≤ ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    have hsq1 : 1 ≤ ‖z‖^2 := hz1.trans hsq
    nlinarith [mul_le_mul_of_nonneg_left hsq he0,
      mul_le_mul_of_nonneg_left hsq1 he0]

theorem remainder_bound_global (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    ‖remainder k x i j‖ ≤ 14 * Real.exp (‖k‖ * ‖x‖) * ‖k‖^2 / (4 * Real.pi * ‖x‖) := by
  let z : ℂ := Complex.I * k * ‖x‖
  have hn : ‖z‖ = ‖k‖ * ‖x‖ := by
    simp [z, norm_mul, abs_of_nonneg (norm_nonneg x)]
  have ha := transverse_bound z
  have hb := radial_bound z
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hc := normalized_coordinate_product_bound x hx i j
  have ht : ‖transverseNumerator z * (if i = j then 1 else 0) +
      radialNumerator z * ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2)‖ ≤ 14 * Real.exp ‖z‖ * ‖z‖^2 := by
    calc
      _ ≤ ‖transverseNumerator z‖ * ‖(if i = j then 1 else 0 : ℂ)‖ +
          ‖radialNumerator z‖ * ‖(x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (4 * Real.exp ‖z‖ * ‖z‖^2) * 1 + (10 * Real.exp ‖z‖ * ‖z‖^2) * 1 :=
        add_le_add (mul_le_mul ha hd (norm_nonneg _) (by positivity))
          (mul_le_mul hb hc (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [remainder_formula k x hx]
  have heq : radialNumerator z * (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2 =
      radialNumerator z * ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2) := by ring
  change ‖(transverseNumerator z * (if i = j then 1 else 0) +
    radialNumerator z * (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2) /
      (4 * Real.pi * (‖x‖ : ℂ)^3)‖ ≤ _
  rw [heq, norm_div]
  have hden : ‖(4 * Real.pi * (‖x‖ : ℂ)^3 : ℂ)‖ = 4 * Real.pi * ‖x‖^3 := by
    simp [norm_mul, norm_pow, abs_of_pos Real.pi_pos]
  rw [hden]
  calc
    _ ≤ (14 * Real.exp ‖z‖ * ‖z‖^2) / (4 * Real.pi * ‖x‖^3) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ = _ := by
      rw [hn, mul_pow]
      field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero]
      ring

theorem remainder_measurable (k : ℂ) (i j : Fin 3) :
    Measurable (fun x : Space => remainder k x i j) := by
  unfold remainder dyadic phi phiHessian radialDD radialD radial
  fun_prop

theorem remainder_zero (k : ℂ) (i j : Fin 3) : remainder k 0 i j = 0 := by
  simp [remainder, dyadic, phi, phiHessian, radialDD, radialD, radial]

/-- A uniform finite-radius bound for the physical complex-frequency remainder. -/
theorem remainder_bound_ball (k : ℂ) (R : ℝ) (x : Space) (hxR : ‖x‖ ≤ R)
    (i j : Fin 3) :
    ‖remainder k x i j‖ ≤
      (14 * Real.exp (‖k‖ * R) * ‖k‖^2 / (4 * Real.pi)) * ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [remainder_zero]
  have hb := remainder_bound_global k x hx i j
  have he : Real.exp (‖k‖ * ‖x‖) ≤ Real.exp (‖k‖ * R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxR (norm_nonneg k))
  apply hb.trans
  have hn : 0 ≤ 14 * ‖k‖^2 := by positivity
  have hd : 0 < 4 * Real.pi * ‖x‖ := by positivity
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he hn) hd.le
  convert hh using 1 <;> field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero] <;> ring

theorem remainder_integrable_ball (k : ℂ) (R : ℝ) (i j : Fin 3) :
    IntegrableOn (fun x : Space => remainder k x i j) (closedBall 0 R) := by
  apply ((KernelIntegrability.inverse_norm_integrable_ball R).const_mul
    (14 * Real.exp (‖k‖ * R) * ‖k‖^2 / (4 * Real.pi))).mono'
    (remainder_measurable k i j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact remainder_bound_ball k R x (by simpa only [mem_closedBall, dist_zero_right] using hx) i j

theorem remainder_memLp_two_ball (k : ℂ) (R : ℝ) (i j : Fin 3) :
    MemLp (fun x : Space => remainder k x i j) 2 (volume.restrict (closedBall 0 R)) := by
  have hm : Measurable (fun x : Space => ‖x‖⁻¹) := continuous_norm.measurable.inv
  have hi : MemLp (fun x : Space => ‖x‖⁻¹) 2 (volume.restrict (closedBall 0 R)) := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using KernelIntegrability.inverse_norm_sq_integrable_ball R
  apply hi.of_le_mul (remainder_measurable k i j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  simpa only [Real.norm_eq_abs, abs_inv, abs_norm] using
    remainder_bound_ball k R x (by simpa only [mem_closedBall, dist_zero_right] using hx) i j

theorem remainder_locallyIntegrable (k : ℂ) (i j : Fin 3) :
    LocallyIntegrable (fun x : Space => remainder k x i j) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (remainder_integrable_ball k R i j).mono_set hR

end OQ14.ComplexDynamicKernel

#print axioms OQ14.ComplexDynamicKernel.dyadic_actual_hessian
#print axioms OQ14.ComplexDynamicKernel.remainder_formula
#print axioms OQ14.ComplexDynamicKernel.dyadic_ofReal
#print axioms OQ14.ComplexDynamicKernel.remainder_ofReal
#print axioms OQ14.ComplexDynamicKernel.exp_norm_bound
#print axioms OQ14.ComplexDynamicKernel.transverse_bound
#print axioms OQ14.ComplexDynamicKernel.radial_bound

#print axioms OQ14.ComplexDynamicKernel.remainder_bound_global
#print axioms OQ14.ComplexDynamicKernel.remainder_measurable
#print axioms OQ14.ComplexDynamicKernel.remainder_zero
#print axioms OQ14.ComplexDynamicKernel.remainder_bound_ball
#print axioms OQ14.ComplexDynamicKernel.remainder_integrable_ball
#print axioms OQ14.ComplexDynamicKernel.remainder_memLp_two_ball
#print axioms OQ14.ComplexDynamicKernel.remainder_locallyIntegrable

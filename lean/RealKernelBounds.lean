import DynamicIntegrability

/-! # Global real-frequency bounds for the actual dynamic Green remainder -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.RealKernelBounds

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel OQ14.DyadicKernel Metric

theorem transverse_bound (z : ℂ) (he : ‖Complex.exp z‖ ≤ 1) :
    ‖transverseNumerator z‖ ≤ 4 * ‖z‖^2 := by
  by_cases hz : ‖z‖ ≤ 1
  · exact transverseNumerator_bound z hz he
  have hz1 : 1 ≤ ‖z‖ := (le_of_not_ge hz)
  have hpoly : ‖-z^2 + z - 1‖ ≤ ‖z‖^2 + ‖z‖ + 1 := by
    calc
      _ ≤ ‖-z^2 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖-z^2‖ + ‖z‖) + 1 := by
        rw [norm_one]
        exact add_le_add_right (norm_add_le (-z^2) z) 1
      _ = _ := by simp
  have htri : ‖transverseNumerator z‖ ≤ ‖Complex.exp z‖ * ‖-z^2 + z - 1‖ + 1 := by
    calc
      _ ≤ ‖Complex.exp z * (-z^2 + z - 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_one]
  have hmul := mul_le_mul he hpoly (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsq : ‖z‖ ≤ ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  nlinarith

theorem radial_bound (z : ℂ) (he : ‖Complex.exp z‖ ≤ 1) :
    ‖radialNumerator z‖ ≤ 10 * ‖z‖^2 := by
  by_cases hz : ‖z‖ ≤ 1
  · exact radialNumerator_bound z hz he
  have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
  have hpoly : ‖z^2 - 3*z + 3‖ ≤ ‖z‖^2 + 3*‖z‖ + 3 := by
    calc
      _ ≤ ‖z^2 - 3*z‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖z^2‖ + ‖3*z‖) + 3 := by
        rw [Complex.norm_ofNat]
        exact add_le_add_right (norm_sub_le (z^2) (3*z)) 3
      _ = _ := by simp [norm_mul]
  have htri : ‖radialNumerator z‖ ≤ ‖Complex.exp z‖ * ‖z^2 - 3*z + 3‖ + 3 := by
    calc
      _ ≤ ‖Complex.exp z * (z^2 - 3*z + 3)‖ + ‖(3 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, Complex.norm_ofNat]
  have hmul := mul_le_mul he hpoly (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsq : ‖z‖ ≤ ‖z‖^2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  nlinarith

theorem remainder_bound_global (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    ‖remainder k x i j‖ ≤ 14 * k^2 / (4 * Real.pi * ‖x‖) := by
  let z : ℂ := Complex.I * k * ‖x‖
  have hn : ‖z‖ = |k| * ‖x‖ := by
    simp [z, norm_mul, abs_of_nonneg (norm_nonneg x)]
  have he : ‖Complex.exp z‖ ≤ 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have ha := transverse_bound z he
  have hb := radial_bound z he
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hc := normalized_coordinate_product_bound x hx i j
  have ht : ‖transverseNumerator z * (if i = j then 1 else 0) +
      radialNumerator z * ((x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2)‖ ≤ 14 * ‖z‖^2 := by
    calc
      _ ≤ ‖transverseNumerator z‖ * ‖(if i = j then 1 else 0 : ℂ)‖ +
          ‖radialNumerator z‖ * ‖(x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (4 * ‖z‖^2) * 1 + (10 * ‖z‖^2) * 1 :=
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
    _ ≤ (14 * ‖z‖^2) / (4 * Real.pi * ‖x‖^3) :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ = _ := by
      rw [hn, mul_pow, sq_abs]
      field_simp [norm_ne_zero_iff.mpr hx, Real.pi_ne_zero]
      ring

theorem remainder_bound_all (k : ℝ) (x : Space) (i j : Fin 3) :
    ‖remainder k x i j‖ ≤ (14 * k^2 / (4 * Real.pi)) * ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [DynamicIntegrability.remainder_zero]
  · simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using
      remainder_bound_global k x hx i j

theorem remainder_integrable_ball (k R : ℝ) (i j : Fin 3) :
    IntegrableOn (fun x : Space => remainder k x i j) (closedBall 0 R) := by
  apply ((KernelIntegrability.inverse_norm_integrable_ball R).const_mul
    (14 * k^2 / (4 * Real.pi))).mono'
    (DynamicIntegrability.remainder_measurable k i j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => remainder_bound_all k x i j)

theorem remainder_locallyIntegrable (k : ℝ) (i j : Fin 3) :
    LocallyIntegrable (fun x : Space => remainder k x i j) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  exact (remainder_integrable_ball k R i j).mono_set hR

theorem hessian_difference_locallyIntegrable (k : ℝ) (i j : Fin 3) :
    LocallyIntegrable (fun x : Space => phiHessian k x i j - phiHessian 0 x i j) := by
  have h := (remainder_locallyIntegrable k i j).sub
    ((KernelIntegrability.phi_locallyIntegrable k).smul
      ((k : ℂ)^2 * (if i = j then 1 else 0)))
  convert h using 1
  ext x
  simp only [remainder, dyadic, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end OQ14.RealKernelBounds

#print axioms OQ14.RealKernelBounds.transverse_bound
#print axioms OQ14.RealKernelBounds.radial_bound
#print axioms OQ14.RealKernelBounds.remainder_bound_global
#print axioms OQ14.RealKernelBounds.remainder_bound_all
#print axioms OQ14.RealKernelBounds.remainder_integrable_ball
#print axioms OQ14.RealKernelBounds.remainder_locallyIntegrable
#print axioms OQ14.RealKernelBounds.hessian_difference_locallyIntegrable

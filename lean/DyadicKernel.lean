import GreenKernel

/-!
# Explicit Maxwell dyadic kernel and its dynamic remainder

The actual Hessian is the one proved in GreenKernel. This module proves
a pointwise 1/r bound after subtracting the static Hessian. Local
integrability, distributional source terms and convolution mapping remain separate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.DyadicKernel

open OQ14.Maxwell OQ14.GreenKernel

def dyadic (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  (k : ℂ)^2 * phi k x * (if i = j then 1 else 0) + phiHessian k x i j

def remainder (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  dyadic k x i j - phiHessian 0 x i j

def transverseNumerator (z : ℂ) : ℂ := Complex.exp z * (-z^2 + z - 1) + 1
def radialNumerator (z : ℂ) : ℂ := Complex.exp z * (z^2 - 3*z + 3) - 3

theorem transverseNumerator_cancel (z : ℂ) :
    transverseNumerator z = -Complex.exp z * z^2 +
      (Complex.exp z - 1) * z - (Complex.exp z - 1 - z) := by
  unfold transverseNumerator
  ring

theorem radialNumerator_cancel (z : ℂ) :
    radialNumerator z = Complex.exp z * z^2 -
      3 * (Complex.exp z - 1) * z + 3 * (Complex.exp z - 1 - z) := by
  unfold radialNumerator
  ring

theorem exp_sub_one_bound (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  have ht := Complex.norm_exp_sub_one_sub_id_le hz
  have hn := norm_add_le (Complex.exp z - 1 - z) z
  have he : Complex.exp z - 1 - z + z = Complex.exp z - 1 := by ring
  rw [he] at hn
  nlinarith [norm_nonneg z]

theorem transverseNumerator_bound (z : ℂ) (hz : ‖z‖ ≤ 1)
    (he : ‖Complex.exp z‖ ≤ 1) : ‖transverseNumerator z‖ ≤ 4 * ‖z‖^2 := by
  rw [transverseNumerator_cancel]
  calc
    _ ≤ ‖-Complex.exp z * z^2‖ + ‖(Complex.exp z - 1) * z‖ +
        ‖Complex.exp z - 1 - z‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ 1 * ‖z‖^2 + (2 * ‖z‖) * ‖z‖ + ‖z‖^2 := by
      simp only [norm_mul, norm_neg, norm_pow]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right he (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (exp_sub_one_bound z hz) (norm_nonneg _)))
        (Complex.norm_exp_sub_one_sub_id_le hz)
    _ = _ := by ring

theorem radialNumerator_bound (z : ℂ) (hz : ‖z‖ ≤ 1)
    (he : ‖Complex.exp z‖ ≤ 1) : ‖radialNumerator z‖ ≤ 10 * ‖z‖^2 := by
  rw [radialNumerator_cancel]
  calc
    _ ≤ ‖Complex.exp z * z^2‖ + ‖3 * (Complex.exp z - 1) * z‖ +
        ‖3 * (Complex.exp z - 1 - z)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ 1 * ‖z‖^2 + (3 * (2 * ‖z‖)) * ‖z‖ + 3 * ‖z‖^2 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right he (sq_nonneg _))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (exp_sub_one_bound z hz) (by norm_num))
          (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_sub_id_le hz) (by norm_num))
    _ = _ := by ring

theorem dyadic_actual_hessian (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dyadic k x i j = (k : ℂ)^2 * phi k x * (if i = j then 1 else 0) +
      dcoord (fun y => dcoord (phi k) y j) x i := by
  rw [phi_second_partial k x hx]
  rfl

theorem remainder_formula (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
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

theorem normalized_coordinate_product_bound (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    ‖(x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2‖ ≤ 1 := by
  have hi : ‖(x i : ℂ)‖ ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x i
  have hj : ‖(x j : ℂ)‖ ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x j
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [norm_div, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  apply (div_le_one (sq_pos_of_pos hr)).2
  simpa only [pow_two, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul hi hj (norm_nonneg (x j : ℂ)) (norm_nonneg x)

/-- The exact dynamic Maxwell kernel has a 1/r bound near its source. -/
theorem remainder_bound (k : ℝ) (x : Space) (hx : x ≠ 0)
    (hsmall : |k| * ‖x‖ ≤ 1) (i j : Fin 3) :
    ‖remainder k x i j‖ ≤ 14 * k^2 / (4 * Real.pi * ‖x‖) := by
  let z : ℂ := Complex.I * k * ‖x‖
  have hn : ‖z‖ = |k| * ‖x‖ := by
    simp [z, norm_mul, abs_of_nonneg (norm_nonneg x)]
  have hz : ‖z‖ ≤ 1 := by rw [hn]; exact hsmall
  have he : ‖Complex.exp z‖ ≤ 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have ha := transverseNumerator_bound z hz he
  have hb := radialNumerator_bound z hz he
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

end OQ14.DyadicKernel

#print axioms OQ14.DyadicKernel.transverseNumerator_cancel
#print axioms OQ14.DyadicKernel.radialNumerator_cancel
#print axioms OQ14.DyadicKernel.exp_sub_one_bound
#print axioms OQ14.DyadicKernel.transverseNumerator_bound
#print axioms OQ14.DyadicKernel.radialNumerator_bound
#print axioms OQ14.DyadicKernel.dyadic_actual_hessian
#print axioms OQ14.DyadicKernel.remainder_formula
#print axioms OQ14.DyadicKernel.normalized_coordinate_product_bound
#print axioms OQ14.DyadicKernel.remainder_bound

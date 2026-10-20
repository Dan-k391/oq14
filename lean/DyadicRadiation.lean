import ScalarRadiation
import ExteriorContinuity

/-! # Transverse far-field estimate for the actual Maxwell dyadic kernel -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DyadicRadiation

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.DyadicKernel
  OQ14.ScalarRadiation

def transverse (x : Space) (i j : Fin 3) : ℂ :=
  (if i = j then 1 else 0) - unitCoordinate i x * unitCoordinate j x

theorem dyadic_factorization (k : ℝ) (z : Space) (hz : z ≠ 0) (i j : Fin 3) :
    dyadic k z i j = phi k z *
      ((k : ℂ)^2 * transverse z i j +
        (Complex.I * k / ‖z‖ - 1 / (‖z‖ : ℂ)^2) *
          ((if i = j then 1 else 0) - 3 * unitCoordinate i z * unitCoordinate j z)) := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold dyadic phi phiHessian radial radialD radialDD transverse unitCoordinate
  push_cast
  generalize hrr : (‖z‖ : ℂ) = r at hr ⊢
  generalize hpp : (Real.pi : ℂ) = p at hp ⊢
  split_ifs <;> field_simp (maxDischargeDepth := 100) [hr, hp]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

theorem transverse_norm_bound (x : Space) (i j : Fin 3) : ‖transverse x i j‖ ≤ 2 := by
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hu : ‖unitCoordinate i x * unitCoordinate j x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (unitCoordinate_norm_le i x) (unitCoordinate_norm_le j x)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (norm_sub_le _ _).trans (by linarith)

theorem transverse_difference (x z : Space) (hx : x ≠ 0) (hz : z ≠ 0)
    (i j : Fin 3) :
    ‖transverse z i j - transverse x i j‖ ≤ 4 * ‖z-x‖ / ‖z‖ := by
  have he : transverse z i j - transverse x i j =
      -(unitCoordinate i z * (unitCoordinate j z - unitCoordinate j x) +
        (unitCoordinate i z - unitCoordinate i x) * unitCoordinate j x) := by
    unfold transverse
    ring
  rw [he, norm_neg]
  calc
    _ ≤ ‖unitCoordinate i z‖ * ‖unitCoordinate j z - unitCoordinate j x‖ +
      ‖unitCoordinate i z - unitCoordinate i x‖ * ‖unitCoordinate j x‖ := by
      simpa only [norm_mul] using norm_add_le
        (unitCoordinate i z * (unitCoordinate j z - unitCoordinate j x))
        ((unitCoordinate i z - unitCoordinate i x) * unitCoordinate j x)
    _ ≤ 1 * (2 * ‖z-x‖ / ‖z‖) + (2 * ‖z-x‖ / ‖z‖) * 1 :=
      add_le_add
        (mul_le_mul (unitCoordinate_norm_le i z) (unitCoordinate_difference j x z hx hz)
          (norm_nonneg _) (by norm_num))
        (mul_le_mul (unitCoordinate_difference i x z hx hz) (unitCoordinate_norm_le j x)
          (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem dyadic_transverse_error (k : ℝ) (z : Space) (hz : z ≠ 0) (i j : Fin 3) :
    ‖dyadic k z i j - (k : ℂ)^2 * phi k z * transverse z i j‖ ≤
      Real.pi⁻¹ * (|k| * (‖z‖⁻¹)^2 + (‖z‖⁻¹)^3) := by
  have he : dyadic k z i j - (k : ℂ)^2 * phi k z * transverse z i j =
      phi k z * (Complex.I * k / ‖z‖ - 1 / (‖z‖ : ℂ)^2) *
        ((if i = j then 1 else 0) - 3 * unitCoordinate i z * unitCoordinate j z) := by
    rw [dyadic_factorization k z hz]
    ring
  have ha : ‖Complex.I * (k : ℂ) / (‖z‖ : ℂ) - 1 / (‖z‖ : ℂ)^2‖ ≤
      |k| * ‖z‖⁻¹ + (‖z‖⁻¹)^2 := by
    apply (norm_sub_le _ _).trans
    simp only [norm_div, norm_mul, norm_inv, Complex.norm_I, one_mul, norm_one, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, div_eq_mul_inv, inv_pow]
    ring_nf
    exact le_rfl
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  have hu : ‖(3 : ℂ) * unitCoordinate i z * unitCoordinate j z‖ ≤ 3 := by
    simp only [norm_mul, Complex.norm_ofNat]
    have hm := mul_le_mul (unitCoordinate_norm_le i z) (unitCoordinate_norm_le j z)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hb : ‖(if i = j then 1 else 0 : ℂ) -
      3 * unitCoordinate i z * unitCoordinate j z‖ ≤ 4 :=
    (norm_sub_le _ _).trans (by linarith)
  rw [he, norm_mul, norm_mul, KernelIntegrability.phi_norm]
  calc
    _ ≤ ((4 * Real.pi)⁻¹ * ‖z‖⁻¹) * (|k| * ‖z‖⁻¹ + (‖z‖⁻¹)^2) * 4 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left ha (by positivity)) hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem dyadic_direction_error (k : ℝ) (x z : Space) (hx : x ≠ 0) (hz : z ≠ 0)
    (i j : Fin 3) :
    ‖dyadic k z i j - (k : ℂ)^2 * phi k z * transverse x i j‖ ≤
      Real.pi⁻¹ * ((k^2 * ‖z-x‖ + |k|) * (‖z‖⁻¹)^2 + (‖z‖⁻¹)^3) := by
  have he : dyadic k z i j - (k : ℂ)^2 * phi k z * transverse x i j =
      (dyadic k z i j - (k : ℂ)^2 * phi k z * transverse z i j) +
        (k : ℂ)^2 * phi k z * (transverse z i j - transverse x i j) := by ring
  rw [he]
  calc
    _ ≤ ‖dyadic k z i j - (k : ℂ)^2 * phi k z * transverse z i j‖ +
      ‖(k : ℂ)^2 * phi k z * (transverse z i j - transverse x i j)‖ := norm_add_le _ _
    _ ≤ Real.pi⁻¹ * (|k| * (‖z‖⁻¹)^2 + (‖z‖⁻¹)^3) +
      k^2 * ((4 * Real.pi)⁻¹ * ‖z‖⁻¹) * (4 * ‖z-x‖ / ‖z‖) := by
      apply add_le_add (dyadic_transverse_error k z hz i j)
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, KernelIntegrability.phi_norm]
      exact mul_le_mul_of_nonneg_left (transverse_difference x z hx hz i j) (by positivity)
    _ = _ := by ring

theorem dyadic_source_error (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2 * R < ‖x‖) (hx2 : 2 ≤ ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖dyadic k (x-y) i j - (k : ℂ)^2 * phi k (x-y) * transverse x i j‖ ≤
      4 * (k^2 * R + |k| + 1) / (Real.pi * ‖x‖^2) := by
  obtain ⟨hx0, hz0, _⟩ := distance_lower_bound R hR x y hx hy
  have hv : 0 ≤ ‖x-y‖⁻¹ := by positivity
  have hi := inverse_distance_bound R hR x y hx hy
  have hxpos : 0 < ‖x‖ := by linarith
  have ht : 2 / ‖x‖ ≤ 1 := (div_le_one hxpos).mpr hx2
  have hsmall : ‖x-y‖⁻¹ ≤ 1 := hi.trans ht
  have hp : (‖x-y‖⁻¹)^3 ≤ (‖x-y‖⁻¹)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x-y‖⁻¹)) (sub_nonneg.mpr hsmall)]
  have hpow := pow_le_pow_left₀ hv hi 2
  have hyR : ‖y‖ ≤ R := mem_closedBall_zero_iff.mp hy
  have hdist : ‖(x-y)-x‖ = ‖y‖ := by
    rw [show x-y-x = -y by abel, norm_neg]
  have hB : k^2 * ‖(x-y)-x‖ + |k| ≤ k^2 * R + |k| := by
    rw [hdist]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hyR (sq_nonneg k)) _
  calc
    _ ≤ Real.pi⁻¹ *
      ((k^2 * ‖(x-y)-x‖ + |k|) * (‖x-y‖⁻¹)^2 + (‖x-y‖⁻¹)^3) :=
      dyadic_direction_error k x (x-y) hx0 hz0 i j
    _ ≤ Real.pi⁻¹ * ((k^2 * R + |k| + 1) * (‖x-y‖⁻¹)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hB (sq_nonneg (‖x-y‖⁻¹))]
    _ ≤ Real.pi⁻¹ * ((k^2 * R + |k| + 1) * (2 / ‖x‖)^2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
    _ = _ := by ring

theorem dyadic_measurable (k : ℝ) (i j : Fin 3) :
    Measurable (fun x => dyadic k x i j) := by
  unfold dyadic phi phiHessian radial radialD radialDD
  fun_prop

theorem response_transverse_error (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ volume)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (x : Space) (hx : 2 * R < ‖x‖) (hx2 : 2 ≤ ‖x‖) (i j : Fin 3) :
    ‖KernelConvolution.response (fun z => dyadic k z i j) ρ x -
      (k : ℂ)^2 * transverse x i j * KernelConvolution.response (phi k) ρ x‖ ≤
      (4 * (k^2 * R + |k| + 1) / (Real.pi * ‖x‖^2)) * (∫ y, ‖ρ y‖) := by
  have hRx : R < ‖x‖ := by linarith
  have hp := NewtonExteriorResponse.source_integrand_integrable (phi k) ρ
    (fun z hz => (phi_contDiffAt k z hz).continuousAt) hρ R hc x hRx
  have hG := NewtonExteriorResponse.source_integrand_integrable _ ρ
    (ExteriorContinuity.dyadic_continuousAt k i j) hρ R hc x hRx
  let a : ℂ := (k : ℂ)^2 * transverse x i j
  let q : Space → ℂ := fun z => dyadic k z i j - a * phi k z
  have hq : Measurable q :=
    (dyadic_measurable k i j).sub (measurable_const.mul (KernelIntegrability.phi_measurable k))
  have he : KernelConvolution.response (fun z => dyadic k z i j) ρ x -
      a * KernelConvolution.response (phi k) ρ x = KernelConvolution.response q ρ x := by
    unfold KernelConvolution.response
    rw [← integral_const_mul, ← integral_sub hG (hp.const_mul a)]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [q]
    ring
  rw [show (k : ℂ)^2 * transverse x i j = a from rfl, he]
  apply response_norm_bound q ρ hq hρ x
  intro y hy
  have hs : y ∈ closedBall 0 R := by
    by_contra hn
    exact hy (hc y hn)
  have heq : q (x-y) = dyadic k (x-y) i j -
      (k : ℂ)^2 * phi k (x-y) * transverse x i j := by dsimp [q, a]; ring
  rw [heq]
  exact dyadic_source_error k R hR x y hx hx2 hs i j

end OQ14.DyadicRadiation

#print axioms OQ14.DyadicRadiation.dyadic_factorization
#print axioms OQ14.DyadicRadiation.transverse_norm_bound
#print axioms OQ14.DyadicRadiation.transverse_difference
#print axioms OQ14.DyadicRadiation.dyadic_transverse_error
#print axioms OQ14.DyadicRadiation.dyadic_direction_error
#print axioms OQ14.DyadicRadiation.dyadic_source_error
#print axioms OQ14.DyadicRadiation.dyadic_measurable
#print axioms OQ14.DyadicRadiation.response_transverse_error

import MagneticResponse

/-! # Quantitative outgoing scalar-kernel estimates outside a compact source -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarRadiation

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
open Filter
open scoped Topology

theorem unitCoordinate_norm_le (i : Fin 3) (x : Space) :
    ‖unitCoordinate i x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [unitCoordinate, hx]
  simp only [unitCoordinate, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm]
  exact (div_le_one (norm_pos_iff.mpr hx)).mpr
    (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i)

theorem unitCoordinate_difference (i : Fin 3) (x z : Space) (hx : x ≠ 0) (hz : z ≠ 0) :
    ‖unitCoordinate i z - unitCoordinate i x‖ ≤ 2 * ‖z-x‖ / ‖z‖ := by
  have hr := norm_pos_iff.mpr hx
  have hd := norm_pos_iff.mpr hz
  have he : z i / ‖z‖ - x i / ‖x‖ =
      (z i-x i) / ‖z‖ + (x i / ‖x‖) * ((‖x‖-‖z‖) / ‖z‖) := by
    field_simp
    ring
  have hc : |z i-x i| ≤ ‖z-x‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (z-x) i
  have hu : |x i / ‖x‖| ≤ 1 := by
    simpa only [unitCoordinate, Complex.norm_real, Real.norm_eq_abs] using unitCoordinate_norm_le i x
  have hn : |‖x‖-‖z‖| ≤ ‖z-x‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le x z
  simp only [unitCoordinate, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he]
  calc
    _ ≤ |(z i-x i) / ‖z‖| + |(x i / ‖x‖) * ((‖x‖-‖z‖) / ‖z‖)| := abs_add_le _ _
    _ ≤ ‖z-x‖ / ‖z‖ + 1 * (‖z-x‖ / ‖z‖) := by
      simp only [abs_div, abs_norm, abs_mul]
      exact add_le_add (div_le_div_of_nonneg_right hc hd.le)
        (mul_le_mul (by simpa only [abs_div, abs_norm] using hu)
          (div_le_div_of_nonneg_right hn hd.le) (by positivity) (by norm_num))
    _ = _ := by ring

theorem gradient_factorization (k : ℝ) (z : Space) (i : Fin 3) :
    phiGradient k z i =
      phi k z * (Complex.I * (k : ℂ) - (‖z‖ : ℂ)⁻¹) * unitCoordinate i z := by
  unfold phiGradient phi radialD radial unitCoordinate
  push_cast
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem gradient_outgoing_bound (k : ℝ) (x z : Space) (hx : x ≠ 0) (hz : z ≠ 0)
    (i : Fin 3) :
    ‖phiGradient k z i - Complex.I * (k : ℂ) * unitCoordinate i x * phi k z‖ ≤
      (4 * Real.pi)⁻¹ * (2 * |k| * ‖z-x‖ + 1) / ‖z‖^2 := by
  have hd := norm_pos_iff.mpr hz
  have he : phiGradient k z i - Complex.I * (k : ℂ) * unitCoordinate i x * phi k z =
      phi k z * (Complex.I * (k : ℂ) * (unitCoordinate i z-unitCoordinate i x) -
        (‖z‖ : ℂ)⁻¹ * unitCoordinate i z) := by
    rw [gradient_factorization k z i]
    ring
  rw [he, norm_mul]
  have hb : ‖Complex.I * (k : ℂ) * (unitCoordinate i z-unitCoordinate i x) -
      (‖z‖ : ℂ)⁻¹ * unitCoordinate i z‖ ≤
      |k| * (2 * ‖z-x‖ / ‖z‖) + ‖z‖⁻¹ := by
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_inv, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_norm]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (unitCoordinate_difference i x z hx hz) (abs_nonneg k))
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (unitCoordinate_norm_le i z) (by positivity : 0 ≤ ‖z‖⁻¹))
  calc
    _ ≤ ‖phi k z‖ * (|k| * (2 * ‖z-x‖ / ‖z‖) + ‖z‖⁻¹) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by
      rw [KernelIntegrability.phi_norm]
      ring

theorem distance_lower_bound (R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) :
    x ≠ 0 ∧ x-y ≠ 0 ∧ ‖x‖/2 ≤ ‖x-y‖ := by
  have hyr : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have h := norm_sub_norm_le x y
  have hxp : 0 < ‖x‖ := by linarith
  have hzp : 0 < ‖x-y‖ := by linarith
  exact ⟨norm_pos_iff.mp hxp, norm_pos_iff.mp hzp, by linarith⟩

theorem source_kernel_outgoing_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (i : Fin 3) :
    ‖phiGradient k (x-y) i - Complex.I * (k : ℂ) * unitCoordinate i x * phi k (x-y)‖ ≤
      (2 * |k| * R + 1) / (Real.pi * ‖x‖^2) := by
  obtain ⟨hx0, hz0, hd⟩ := distance_lower_bound R hR x y hx hy
  have hyr : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hxy : ‖x-y-x‖ = ‖y‖ := by
    rw [show x-y-x = -y by abel, norm_neg]
  have hn := gradient_outgoing_bound k x (x-y) hx0 hz0 i
  rw [hxy] at hn
  have hnum : (4 * Real.pi)⁻¹ * (2 * |k| * ‖y‖ + 1) ≤
      (4 * Real.pi)⁻¹ * (2 * |k| * R + 1) :=
    mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left hyr (by positivity)) 1) (by positivity)
  have hsq : (‖x‖/2)^2 ≤ ‖x-y‖^2 :=
    pow_le_pow_left₀ (by positivity) hd 2
  have hp : 0 < (‖x‖/2)^2 := by positivity
  apply hn.trans
  calc
    _ ≤ ((4 * Real.pi)⁻¹ * (2 * |k| * R + 1)) / (‖x‖/2)^2 :=
      div_le_div₀ (by positivity) hnum hp hsq
    _ = _ := by ring

theorem source_integrand_integrable (q ρ : Space → ℂ) (hq : Measurable q)
    (hρ : Integrable ρ) (x : Space) (C : ℝ)
    (hb : ∀ y, ρ y ≠ 0 → ‖q (x-y)‖ ≤ C) :
    Integrable (fun y => ρ y * q (x-y)) := by
  apply (hρ.norm.const_mul C).mono'
    (hρ.aestronglyMeasurable.mul
      (hq.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  filter_upwards with y
  change ‖ρ y * q (x-y)‖ ≤ C * ‖ρ y‖
  by_cases hy : ρ y = 0
  · simp [hy]
  · rw [norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb y hy) (norm_nonneg _)

theorem response_norm_bound (q ρ : Space → ℂ) (hq : Measurable q)
    (hρ : Integrable ρ) (x : Space) (C : ℝ)
    (hb : ∀ y, ρ y ≠ 0 → ‖q (x-y)‖ ≤ C) :
    ‖response q ρ x‖ ≤ C * (∫ y, ‖ρ y‖) := by
  have hi := source_integrand_integrable q ρ hq hρ x C hb
  calc
    _ ≤ ∫ y, ‖ρ y * q (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * ‖ρ y‖ := by
      apply integral_mono_ae hi.norm (hρ.norm.const_mul C)
      filter_upwards with y
      by_cases hy : ρ y = 0
      · simp [hy]
      · rw [norm_mul, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hb y hy) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem inverse_distance_bound (R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) :
    ‖x-y‖⁻¹ ≤ 2 / ‖x‖ := by
  obtain ⟨hx0, _, hd⟩ := distance_lower_bound R hR x y hx hy
  have hp : 0 < ‖x‖/2 := by positivity
  have h := one_div_le_one_div_of_le hp hd
  convert h using 1 <;> field_simp

theorem phi_source_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) :
    ‖phi k (x-y)‖ ≤ (4 * Real.pi)⁻¹ * (2 / ‖x‖) := by
  rw [KernelIntegrability.phi_norm]
  exact mul_le_mul_of_nonneg_left (inverse_distance_bound R hR x y hx hy) (by positivity)

theorem gradient_source_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (i : Fin 3) :
    ‖phiGradient k (x-y) i‖ ≤
      (4 * Real.pi)⁻¹ * (|k| * (2/‖x‖) + (2/‖x‖)^2) := by
  apply (KernelGradient.gradient_bound k (x-y) i).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := inverse_distance_bound R hR x y hx hy
  exact add_le_add (mul_le_mul_of_nonneg_left h (abs_nonneg k))
    (pow_le_pow_left₀ (by positivity) h 2)

/-- The actual scalar source response and the actual gradient response satisfy
a uniform inverse-square outgoing estimate outside twice the source radius. -/
theorem response_outgoing_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (i : Fin 3) :
    ‖response (fun z => phiGradient k z i) ρ x -
      Complex.I * (k : ℂ) * unitCoordinate i x * response (phi k) ρ x‖ ≤
      ((2 * |k| * R + 1) / (Real.pi * ‖x‖^2)) * (∫ y, ‖ρ y‖) := by
  have hs (y : Space) (hy : ρ y ≠ 0) : y ∈ closedBall 0 R := by
    by_contra hn
    exact hy (hc y hn)
  have hp := source_integrand_integrable (phi k) ρ (KernelIntegrability.phi_measurable k)
    hρ x ((4 * Real.pi)⁻¹ * (2 / ‖x‖)) (fun y hy => phi_source_bound k R hR x y hx (hs y hy))
  have hg := source_integrand_integrable (fun z => phiGradient k z i) ρ
    (KernelGradient.gradient_measurable k i) hρ x
    ((4 * Real.pi)⁻¹ * (|k| * (2/‖x‖) + (2/‖x‖)^2))
    (fun y hy => gradient_source_bound k R hR x y hx (hs y hy) i)
  let a : ℂ := Complex.I * (k : ℂ) * unitCoordinate i x
  let q : Space → ℂ := fun z => phiGradient k z i - a * phi k z
  have hq : Measurable q :=
    (KernelGradient.gradient_measurable k i).sub
      (measurable_const.mul (KernelIntegrability.phi_measurable k))
  have he : response (fun z => phiGradient k z i) ρ x - a * response (phi k) ρ x =
      response q ρ x := by
    unfold response
    rw [← integral_const_mul, ← integral_sub hg (hp.const_mul a)]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [q]
    ring
  rw [show Complex.I * (k : ℂ) * unitCoordinate i x = a from rfl, he]
  exact response_norm_bound q ρ hq hρ x _
    (fun y hy => source_kernel_outgoing_bound k R hR x y hx (hs y hy) i)

/-- Along every path escaping to spatial infinity, the scalar response's
outgoing gradient defect vanishes after multiplication by the radius. -/
theorem response_outgoing_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (i : Fin 3) :
    Tendsto (fun t => (‖γ t‖ : ℂ) *
      (response (fun z => phiGradient k z i) ρ (γ t) -
        Complex.I * (k : ℂ) * unitCoordinate i (γ t) * response (phi k) ρ (γ t)))
      atTop (𝓝 0) := by
  let C : ℝ := ((2 * |k| * R + 1) / Real.pi) * (∫ y, ‖ρ y‖)
  have hl : Tendsto (fun t => C * (‖γ t‖)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hγ) :
        Tendsto (fun t => C * (‖γ t‖)⁻¹) atTop (𝓝 (C * 0)))
  apply squeeze_zero_norm' _ hl
  filter_upwards [hγ.eventually (eventually_gt_atTop (2*R))] with t ht
  have hp : 0 < ‖γ t‖ := lt_of_le_of_lt (by positivity) ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  calc
    _ ≤ ‖γ t‖ * (((2 * |k| * R + 1) / (Real.pi * ‖γ t‖^2)) *
      (∫ y, ‖ρ y‖)) :=
      mul_le_mul_of_nonneg_left (response_outgoing_bound k R hR ρ hρ hc (γ t) ht i)
        (norm_nonneg _)
    _ = C * (‖γ t‖)⁻¹ := by
      dsimp [C]
      field_simp
      <;> ring

end OQ14.ScalarRadiation

#print axioms OQ14.ScalarRadiation.unitCoordinate_norm_le
#print axioms OQ14.ScalarRadiation.unitCoordinate_difference
#print axioms OQ14.ScalarRadiation.gradient_factorization
#print axioms OQ14.ScalarRadiation.gradient_outgoing_bound
#print axioms OQ14.ScalarRadiation.distance_lower_bound
#print axioms OQ14.ScalarRadiation.source_kernel_outgoing_bound
#print axioms OQ14.ScalarRadiation.source_integrand_integrable
#print axioms OQ14.ScalarRadiation.response_norm_bound
#print axioms OQ14.ScalarRadiation.inverse_distance_bound
#print axioms OQ14.ScalarRadiation.phi_source_bound
#print axioms OQ14.ScalarRadiation.gradient_source_bound
#print axioms OQ14.ScalarRadiation.response_outgoing_bound
#print axioms OQ14.ScalarRadiation.response_outgoing_limit

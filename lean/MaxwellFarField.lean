import ScalarFarField
import MaxwellRadiation

/-! # Actual electric and magnetic far-field amplitudes -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaxwellFarField

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.GreenKernel
  OQ14.KernelConvolution OQ14.ScalarRadiation OQ14.DyadicRadiation
  OQ14.MaxwellRadiation
open scoped Topology

def factor (k r : ℝ) : ℂ := (r : ℂ) * Complex.exp (-Complex.I * k * r)

def potentialAmplitude (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) : Vector :=
  fun j => ScalarFarField.amplitude k (ρ j) n

def electricAmplitude (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) : Vector :=
  fun i => ∑ j : Fin 3, (k : ℂ)^2 * transverse n i j * potentialAmplitude k ρ n j

def magneticAmplitude (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) : Vector :=
  fun i => (k : ℂ)^2 * crossProduct (direction n) (potentialAmplitude k ρ n) i

theorem factor_norm (k r : ℝ) (hr : 0 < r) : ‖factor k r‖ = r := by
  simp only [factor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    Complex.norm_exp]
  simp

theorem ray_direction (n : Space) (hn : ‖n‖ = 1) (r : ℝ) (hr : 0 < r) :
    direction (r • n) = direction n := by
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr]
  ext i
  simp only [direction, unitCoordinate, PiLp.smul_apply, smul_eq_mul, hnr, hn, div_one]
  congr 1
  field_simp

theorem ray_transverse (n : Space) (hn : ‖n‖ = 1) (r : ℝ) (hr : 0 < r)
    (i j : Fin 3) : transverse (r • n) i j = transverse n i j := by
  have hi := congrFun (ray_direction n hn r hr) i
  have hj := congrFun (ray_direction n hn r hr) j
  simp only [direction] at hi hj
  simp only [transverse, hi, hj]

theorem scaled_error_limit (k C B : ℝ) (f : ℝ → ℂ)
    (hf : ∀ r, B < r → ‖f r‖ ≤ C / r^2) :
    Tendsto (fun r : ℝ => factor k r * f r) atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => C * r⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun r : ℝ => C * r⁻¹) atTop (𝓝 (C * 0)))
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop B, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  rw [norm_mul, factor_norm k r hr0]
  calc
    _ ≤ r * (C/r^2) := mul_le_mul_of_nonneg_left (hf r hr) hr0.le
    _ = C * r⁻¹ := by field_simp; ring

theorem leading_electric_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r * leadingElectric k ρ (r • n) i) atTop
      (𝓝 (electricAmplitude k ρ n i)) := by
  have h (j : Fin 3) := (ScalarFarField.response_far_limit k R hR (ρ j) (hρ j)
    (hc j) n hn).const_mul ((k : ℂ)^2 * transverse n i j)
  have ht := tendsto_finset_sum Finset.univ (fun j _ => h j)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [leadingElectric, potential, Finset.mul_sum, ray_transverse n hn r hr]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [factor]
  ring

theorem leading_magnetic_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r * leadingMagnetic k ρ (r • n) i) atTop
      (𝓝 (magneticAmplitude k ρ n i)) := by
  have h (j : Fin 3) := ScalarFarField.response_far_limit k R hR (ρ j) (hρ j) (hc j) n hn
  have ht := (((h (WeakCurl.previous i)).const_mul (direction n (WeakCurl.next i))).sub
    ((h (WeakCurl.next i)).const_mul (direction n (WeakCurl.previous i)))).const_mul ((k : ℂ)^2)
  simp only [magneticAmplitude, cross_component, potentialAmplitude]
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [leadingMagnetic, cross_component, potential, ray_direction n hn r hr]
  dsimp [factor]
  ring

theorem electric_error_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r *
      (ExteriorContinuity.electric k ρ (r • n) i - leadingElectric k ρ (r • n) i))
      atTop (𝓝 0) := by
  apply scaled_error_limit k (4 * (k^2 * R + |k| + 1) / Real.pi * sourceMass ρ)
    (max (2*R) 2)
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hr))
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hb := electric_transverse_bound k R hR ρ hρ hc (r • n)
    (by rw [hnr]; exact lt_of_le_of_lt (le_max_left _ _) hr)
    (by rw [hnr]; exact (lt_of_le_of_lt (le_max_right _ _) hr).le) i
  rw [hnr] at hb
  convert hb using 1
  dsimp [sourceMass]
  ring

theorem magnetic_error_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r *
      (MagneticResponse.magnetic k ρ (r • n) i - leadingMagnetic k ρ (r • n) i))
      atTop (𝓝 0) := by
  apply scaled_error_limit k (2 * |k| * (2 * |k| * R + 1) / Real.pi * sourceMass ρ) (2*R)
  intro r hr
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hnr : ‖r • n‖ = r := by simp [norm_smul, hn, abs_of_pos hr0]
  have hb := magnetic_transverse_bound k R hR ρ hρ hc (r • n) (by rwa [hnr]) i
  rw [hnr] at hb
  convert hb using 1
  ring

theorem electric_far_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r * ExteriorContinuity.electric k ρ (r • n) i)
      atTop (𝓝 (electricAmplitude k ρ n i)) := by
  have ht := (electric_error_limit k R hR ρ hρ hc n hn i).add
    (leading_electric_limit k R hR ρ hρ hc n hn i)
  simpa only [mul_sub, sub_add_cancel, zero_add] using ht

theorem magnetic_far_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => factor k r * MagneticResponse.magnetic k ρ (r • n) i)
      atTop (𝓝 (magneticAmplitude k ρ n i)) := by
  have ht := (magnetic_error_limit k R hR ρ hρ hc n hn i).add
    (leading_magnetic_limit k R hR ρ hρ hc n hn i)
  simpa only [mul_sub, sub_add_cancel, zero_add] using ht

theorem electric_far_vector_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => factor k r • ExteriorContinuity.electric k ρ (r • n))
      atTop (𝓝 (electricAmplitude k ρ n)) :=
  tendsto_pi_nhds.mpr (electric_far_limit k R hR ρ hρ hc n hn)

theorem magnetic_far_vector_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (n : Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => factor k r • MagneticResponse.magnetic k ρ (r • n))
      atTop (𝓝 (magneticAmplitude k ρ n)) :=
  tendsto_pi_nhds.mpr (magnetic_far_limit k R hR ρ hρ hc n hn)

theorem amplitude_formula (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) (i : Fin 3) :
    electricAmplitude k ρ n i = (k : ℂ)^2 *
      (potentialAmplitude k ρ n i - dot (direction n) (potentialAmplitude k ρ n) * direction n i) := by
  fin_cases i <;> simp [electricAmplitude, Fin.sum_univ_three, transverse, direction, dot] <;> ring

theorem amplitude_tangential_relation (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) :
    crossProduct (direction n) (electricAmplitude k ρ n) = magneticAmplitude k ρ n := by
  ext i
  fin_cases i <;> simp [cross_apply, amplitude_formula, magneticAmplitude] <;> ring

theorem amplitude_transverse (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) (hn : ‖n‖ = 1) :
    dot (direction n) (electricAmplitude k ρ n) = 0 := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have hs := direction_dot n hn0
  have he : dot (direction n) (electricAmplitude k ρ n) =
      (k : ℂ)^2 * dot (direction n) (potentialAmplitude k ρ n) *
        (1 - dot (direction n) (direction n)) := by
    simp only [dot, amplitude_formula]
    ring
  rw [he, hs, sub_self, mul_zero]

end OQ14.MaxwellFarField

#print axioms OQ14.MaxwellFarField.factor_norm
#print axioms OQ14.MaxwellFarField.ray_direction
#print axioms OQ14.MaxwellFarField.ray_transverse
#print axioms OQ14.MaxwellFarField.scaled_error_limit
#print axioms OQ14.MaxwellFarField.leading_electric_limit
#print axioms OQ14.MaxwellFarField.leading_magnetic_limit
#print axioms OQ14.MaxwellFarField.electric_error_limit
#print axioms OQ14.MaxwellFarField.magnetic_error_limit
#print axioms OQ14.MaxwellFarField.electric_far_limit
#print axioms OQ14.MaxwellFarField.magnetic_far_limit
#print axioms OQ14.MaxwellFarField.electric_far_vector_limit
#print axioms OQ14.MaxwellFarField.magnetic_far_vector_limit
#print axioms OQ14.MaxwellFarField.amplitude_formula
#print axioms OQ14.MaxwellFarField.amplitude_tangential_relation
#print axioms OQ14.MaxwellFarField.amplitude_transverse

import AngularPowerZero

/-! # Actual unphased spherical electric and magnetic energy limits -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.AngularEnergy

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.MaxwellFarField OQ14.FarFieldPower
open scoped Topology

theorem energy_continuous : Continuous energy := by
  unfold energy
  fun_prop

theorem energy_smul (a : ℂ) (v : Vector) :
    energy (a • v) = Complex.normSq a * energy v := by
  simp only [energy, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  ring

theorem scaled_energy (k r : ℝ) (hr : 0 < r) (v : Vector) :
    energy (factor k r • v) = r^2 * energy v := by
  rw [energy_smul, Complex.normSq_eq_norm_sq, factor_norm k r hr]

theorem energy_bound (v : Vector) (C : ℝ) (_hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) :
    energy v ≤ 3*C^2 := by
  have h (i : Fin 3) : Complex.normSq (v i) ≤ C^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
  unfold energy
  linarith [h 0, h 1, h 2]

def sphericalEnergy (E : Field) (r : ℝ) : ℝ :=
  ∫ n : Sphere, r^2 * energy (E (r • (n : Space))) ∂angularMeasure

theorem spherical_energy_limit (k : ℝ) (E : Field) (A : Sphere → Vector)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r * E (r • (n : Space)) i‖ ≤ C)
    (hl : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space)))
      atTop (𝓝 (A n))) :
    Tendsto (sphericalEnergy E) atTop (𝓝 (∫ n : Sphere, energy (A n) ∂angularMeasure)) := by
  obtain ⟨C,hC,hb⟩ := hb
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ : Sphere => 3*C^2)
  · filter_upwards [hc] with r hr
    exact (continuous_const.mul (energy_continuous.comp hr)).aestronglyMeasurable
  · filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (energy_nonnegative _)),
      ← scaled_energy k r hr0]
    exact energy_bound _ C hC (hr n)
  · exact integrable_const _
  · filter_upwards with n
    apply (energy_continuous.tendsto (A n) |>.comp (hl n)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact scaled_energy k r hr _

theorem electric_spherical_energy_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Tendsto (sphericalEnergy (ExteriorContinuity.electric k ρ)) atTop
      (𝓝 (∫ n : Sphere, energy (electricAmplitude k ρ (n : Space)) ∂angularMeasure)) := by
  apply spherical_energy_limit k _ _
  · filter_upwards [eventually_gt_atTop R] with r hr
    exact (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).1
  · obtain ⟨C,hC,h⟩ := actual_fields_uniform_bound k R hR ρ hρ hs
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_gt_atTop (max (2*R) 2)] with r hr
    exact fun n i => (h r hr n (sphere_norm n) i).1
  · exact fun n => electric_far_vector_limit k R hR ρ hρ hs n (sphere_norm n)

theorem magnetic_spherical_energy_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Tendsto (sphericalEnergy (MagneticResponse.magnetic k ρ)) atTop
      (𝓝 (∫ n : Sphere, energy (magneticAmplitude k ρ (n : Space)) ∂angularMeasure)) := by
  apply spherical_energy_limit k _ _
  · filter_upwards [eventually_gt_atTop R] with r hr
    exact (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).2
  · obtain ⟨C,hC,h⟩ := actual_fields_uniform_bound k R hR ρ hρ hs
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_gt_atTop (max (2*R) 2)] with r hr
    exact fun n i => (h r hr n (sphere_norm n) i).2
  · exact fun n => magnetic_far_vector_limit k R hR ρ hρ hs n (sphere_norm n)

theorem spherical_energies_zero_of_farPower_zero (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (hz : farPower k ρ = 0) :
    Tendsto (sphericalEnergy (ExteriorContinuity.electric k ρ)) atTop (𝓝 0) ∧
      Tendsto (sphericalEnergy (MagneticResponse.magnetic k ρ)) atTop (𝓝 0) := by
  have ha := (AngularPowerZero.farPower_zero_iff_both_amplitudes k ρ hρ).mp hz
  have he : (∫ n : Sphere, energy (electricAmplitude k ρ (n : Space)) ∂angularMeasure) = 0 := by
    simp only [fun n => (ha n).1, energy, Pi.zero_apply, map_zero, add_zero, integral_zero]
  have hh : (∫ n : Sphere, energy (magneticAmplitude k ρ (n : Space)) ∂angularMeasure) = 0 := by
    simp only [fun n => (ha n).2, energy, Pi.zero_apply, map_zero, add_zero, integral_zero]
  exact ⟨he ▸ electric_spherical_energy_limit k R hR ρ hρ hs,
    hh ▸ magnetic_spherical_energy_limit k R hR ρ hρ hs⟩

end OQ14.AngularEnergy

#print axioms OQ14.AngularEnergy.energy_continuous
#print axioms OQ14.AngularEnergy.energy_smul
#print axioms OQ14.AngularEnergy.scaled_energy
#print axioms OQ14.AngularEnergy.energy_bound
#print axioms OQ14.AngularEnergy.spherical_energy_limit
#print axioms OQ14.AngularEnergy.electric_spherical_energy_limit
#print axioms OQ14.AngularEnergy.magnetic_spherical_energy_limit
#print axioms OQ14.AngularEnergy.spherical_energies_zero_of_farPower_zero

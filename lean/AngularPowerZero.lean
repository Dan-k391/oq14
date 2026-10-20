import AngularPower
import SphereMeasure

/-!
Zero actual outgoing spherical power forces both Maxwell far-field amplitudes
to vanish in every direction. Actual spherical support is supplied by the
proved positivity of Euclidean volume.toSphere on nonempty open patches.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OQ14.AngularPowerZero
open MeasureTheory Metric Filter OQ14.Maxwell OQ14.MaxwellFarField OQ14.AngularPower
open scoped Topology

instance angularMeasure_openPos : Measure.IsOpenPosMeasure angularMeasure :=
  SphereMeasure.volume_toSphere_openPos

theorem farPower_zero_iff_pointwise (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    farPower k ρ = 0 ↔ ∀ n : Sphere, electricAmplitude k ρ (n : Space) = 0 := by
  rw [farPower_zero_iff k ρ hρ]
  constructor
  · intro h
    have he : (fun n : Sphere => electricAmplitude k ρ (n : Space)) = 0 :=
      Measure.eq_of_ae_eq h (electric_amplitude_continuous k ρ hρ) continuous_const
    exact fun n => congrFun he n
  · exact fun h => Filter.Eventually.of_forall h

theorem farPower_zero_iff_unit (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    farPower k ρ = 0 ↔ ∀ n : Space, ‖n‖ = 1 → electricAmplitude k ρ n = 0 := by
  rw [farPower_zero_iff_pointwise k ρ hρ]
  constructor
  · intro h n hn
    exact h ⟨n, by simpa only [mem_sphere, dist_zero_right] using hn⟩
  · intro h n
    exact h n (sphere_norm n)

theorem magnetic_zero_of_electric_zero (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space)
    (he : electricAmplitude k ρ n = 0) : magneticAmplitude k ρ n = 0 := by
  rw [← amplitude_tangential_relation, he]
  ext i
  fin_cases i <;> simp [cross_apply]

theorem farPower_zero_iff_both_amplitudes (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) :
    farPower k ρ = 0 ↔ ∀ n : Sphere,
      electricAmplitude k ρ (n : Space) = 0 ∧ magneticAmplitude k ρ (n : Space) = 0 := by
  rw [farPower_zero_iff_pointwise k ρ hρ]
  constructor
  · intro h n
    exact ⟨h n, magnetic_zero_of_electric_zero k ρ n (h n)⟩
  · intro h n
    exact (h n).1

theorem zero_power_limit_iff_pointwise (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Tendsto (fun r => sphericalPower k r ρ) atTop (𝓝 0) ↔
      ∀ n : Sphere, electricAmplitude k ρ (n : Space) = 0 := by
  constructor
  · intro hz
    apply (farPower_zero_iff_pointwise k ρ hρ).mp
    exact tendsto_nhds_unique (actual_spherical_power_limit k R hR ρ hρ hc) hz
  · intro h
    have hz := (farPower_zero_iff_pointwise k ρ hρ).mpr h
    simpa only [hz] using actual_spherical_power_limit k R hR ρ hρ hc

theorem zero_power_limit_both_amplitudes (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hz : Tendsto (fun r => sphericalPower k r ρ) atTop (𝓝 0)) :
    ∀ n : Space, ‖n‖ = 1 →
      electricAmplitude k ρ n = 0 ∧ magneticAmplitude k ρ n = 0 := by
  have he := (zero_power_limit_iff_pointwise k R hR ρ hρ hc).mp hz
  have hf := (farPower_zero_iff_pointwise k ρ hρ).mpr he
  intro n hn
  have he' := (farPower_zero_iff_unit k ρ hρ).mp hf n hn
  exact ⟨he', magnetic_zero_of_electric_zero k ρ n he'⟩

end OQ14.AngularPowerZero

#print axioms OQ14.AngularPowerZero.farPower_zero_iff_pointwise
#print axioms OQ14.AngularPowerZero.farPower_zero_iff_unit
#print axioms OQ14.AngularPowerZero.magnetic_zero_of_electric_zero
#print axioms OQ14.AngularPowerZero.farPower_zero_iff_both_amplitudes
#print axioms OQ14.AngularPowerZero.zero_power_limit_iff_pointwise
#print axioms OQ14.AngularPowerZero.zero_power_limit_both_amplitudes

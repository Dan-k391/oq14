import AngularEnergy
import RadialMoment

/-! # Actual scalar component mass from the spherical Maxwell energy -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ComponentAngularEnergy

open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.AngularPower
  OQ14.AngularEnergy OQ14.RadialMoment OQ14.FarFieldPower
open scoped Topology

theorem component_norm_sq_le_energy (v : Vector) (i : Fin 3) : ‖v i‖^2 ≤ energy v := by
  have h0 := Complex.normSq_nonneg (v 0)
  have h1 := Complex.normSq_nonneg (v 1)
  have h2 := Complex.normSq_nonneg (v 2)
  rw [← Complex.normSq_eq_norm_sq]
  fin_cases i
  · change Complex.normSq (v 0) ≤ Complex.normSq (v 0)+Complex.normSq (v 1)+Complex.normSq (v 2)
    linarith
  · change Complex.normSq (v 1) ≤ Complex.normSq (v 0)+Complex.normSq (v 1)+Complex.normSq (v 2)
    linarith
  · change Complex.normSq (v 2) ≤ Complex.normSq (v 0)+Complex.normSq (v 1)+Complex.normSq (v 2)
    linarith

theorem sphericalMass_nonnegative (u : Space → ℂ) (r : ℝ) : 0 ≤ sphericalMass u r :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg r) (sq_nonneg _))

theorem component_mass_le_energy (E : Field) (r : ℝ)
    (hE : Continuous (fun n : Sphere => E (r • (n : Space)))) (i : Fin 3) :
    sphericalMass (fun x => E x i) r ≤ sphericalEnergy E r := by
  have hc : Continuous (fun n : Sphere => r^2*‖E (r • (n : Space)) i‖^2) :=
    continuous_const.mul (((continuous_apply i).comp hE).norm.pow 2)
  have hv : Continuous (fun n : Sphere => r^2*energy (E (r • (n : Space)))) :=
    continuous_const.mul (energy_continuous.comp hE)
  apply integral_mono
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  intro n
  exact mul_le_mul_of_nonneg_left (component_norm_sq_le_energy _ i) (sq_nonneg r)

theorem component_mass_tendsto_zero (E : Field)
    (hE : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))))
    (henergy : Tendsto (sphericalEnergy E) atTop (𝓝 0)) (i : Fin 3) :
    Tendsto (sphericalMass (fun x => E x i)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (sphericalMass_nonnegative _)) _ henergy
  filter_upwards [hE] with r hr
  exact component_mass_le_energy E r hr i

theorem electric_component_mass_le (k R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (i : Fin 3) :
    sphericalMass (fun x => ExteriorContinuity.electric k ρ x i) r ≤
      sphericalEnergy (ExteriorContinuity.electric k ρ) r :=
  component_mass_le_energy _ r (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).1 i

theorem magnetic_component_mass_le (k R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (i : Fin 3) :
    sphericalMass (fun x => MagneticResponse.magnetic k ρ x i) r ≤
      sphericalEnergy (MagneticResponse.magnetic k ρ) r :=
  component_mass_le_energy _ r (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).2 i

theorem electric_component_mass_zero_of_farPower_zero (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (hz : farPower k ρ = 0) (i : Fin 3) :
    Tendsto (sphericalMass (fun x => ExteriorContinuity.electric k ρ x i)) atTop (𝓝 0) := by
  apply component_mass_tendsto_zero
    (ExteriorContinuity.electric k ρ) _
    (spherical_energies_zero_of_farPower_zero k R hR ρ hρ hs hz).1 i
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).1

theorem magnetic_component_mass_zero_of_farPower_zero (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (hz : farPower k ρ = 0) (i : Fin 3) :
    Tendsto (sphericalMass (fun x => MagneticResponse.magnetic k ρ x i)) atTop (𝓝 0) := by
  apply component_mass_tendsto_zero
    (MagneticResponse.magnetic k ρ) _
    (spherical_energies_zero_of_farPower_zero k R hR ρ hρ hs hz).2 i
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (actual_fields_sphere_continuous k R r hR hr ρ hρ hs).2

theorem component_masses_zero_of_farPower_zero (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (hz : farPower k ρ = 0) :
    ∀ i : Fin 3,
      Tendsto (sphericalMass (fun x => ExteriorContinuity.electric k ρ x i)) atTop (𝓝 0) ∧
      Tendsto (sphericalMass (fun x => MagneticResponse.magnetic k ρ x i)) atTop (𝓝 0) :=
  fun i => ⟨electric_component_mass_zero_of_farPower_zero k R hR ρ hρ hs hz i,
    magnetic_component_mass_zero_of_farPower_zero k R hR ρ hρ hs hz i⟩

end OQ14.ComponentAngularEnergy

#print axioms OQ14.ComponentAngularEnergy.component_norm_sq_le_energy
#print axioms OQ14.ComponentAngularEnergy.sphericalMass_nonnegative
#print axioms OQ14.ComponentAngularEnergy.component_mass_le_energy
#print axioms OQ14.ComponentAngularEnergy.component_mass_tendsto_zero
#print axioms OQ14.ComponentAngularEnergy.electric_component_mass_le
#print axioms OQ14.ComponentAngularEnergy.magnetic_component_mass_le
#print axioms OQ14.ComponentAngularEnergy.electric_component_mass_zero_of_farPower_zero
#print axioms OQ14.ComponentAngularEnergy.magnetic_component_mass_zero_of_farPower_zero
#print axioms OQ14.ComponentAngularEnergy.component_masses_zero_of_farPower_zero

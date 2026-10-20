import PolarIntegration
import RadialPowerTest
import RadialWeight
import MaterialPower

/-! # Radial flux identities from actual weak Maxwell power conservation -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.RadialFlux

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.FarFieldPower OQ14.RadialPowerTest OQ14.WeakConservation
open scoped Topology ENNReal

def flux (E H : Field) (r : ℝ) : ℝ :=
  ∫ n : Sphere, r^2 * radialPower (n : Space) (E (r • (n : Space)))
    (H (r • (n : Space))) ∂angularMeasure

def weight (a r : ℝ) : ℝ := (2/a^2) * r * beta (r^2/a^2)

theorem integrable_polar (f : Space → ℝ) (hf : Integrable f) :
    IntegrableOn (fun r : ℝ => r^2 *
      (∫ n : Sphere, f (r • (n : Space)) ∂angularMeasure)) (Set.Ioi 0) := by
  have hi := (PolarIntegration.integrable_polar_product f hf).integral_prod_right
  change Integrable _ (Measure.volumeIoiPow 2) at hi
  simp only [Measure.volumeIoiPow, ENNReal.ofReal] at hi
  rw [integrable_withDensity_iff_integrable_smul
    (measurable_subtype_coe.pow_const _).real_toNNReal] at hi
  apply (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mpr
  convert hi using 1
  ext r
  simp [NNReal.smul_def, Real.coe_toNNReal, sq_nonneg]

theorem ray_testPower (a : ℝ) (ha : 0 < a) (E H : Field) (r : ℝ) (hr : 0 < r)
    (n : Sphere) :
    r^2 * testPower (scaledCutoff a ha) E H (r • (n : Space)) =
      -(weight a r) * (r^2 * radialPower (n : Space)
        (E (r • (n : Space))) (H (r • (n : Space)))) := by
  rw [scaledCutoff_testPower]
  have hn : ‖r • (n : Space)‖ = r := by
    simp [norm_smul, sphere_norm, abs_of_pos hr]
  have hd := MaxwellFarField.ray_direction (n : Space) (sphere_norm n) r hr
  simp only [hn, radialPower, hd, weight]
  ring

theorem angular_testPower (a : ℝ) (ha : 0 < a) (E H : Field) (r : ℝ) (hr : 0 < r) :
    r^2 * (∫ n : Sphere, testPower (scaledCutoff a ha) E H (r • (n : Space))
      ∂angularMeasure) = -(weight a r) * flux E H r := by
  rw [← integral_const_mul]
  simp_rw [ray_testPower a ha E H r hr]
  rw [integral_const_mul]
  rfl

theorem weighted_flux (a : ℝ) (ha : 0 < a) (E H : Field)
    (hi : Integrable (testPower (scaledCutoff a ha) E H))
    (hz : (∫ x, testPower (scaledCutoff a ha) E H x) = 0) :
    IntegrableOn (fun r => weight a r * flux E H r) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi 0, weight a r * flux E H r) = 0 := by
  have he (r : ℝ) (hr : r ∈ Set.Ioi (0 : ℝ)) :
      r^2 * (∫ n : Sphere, testPower (scaledCutoff a ha) E H (r • (n : Space))
        ∂angularMeasure) = -(weight a r * flux E H r) := by
    rw [angular_testPower a ha E H r hr, neg_mul]
  have hin := (integrable_polar _ hi).congr_fun he measurableSet_Ioi
  constructor
  · have hn := hin.neg
    change Integrable (fun r => -(-(weight a r * flux E H r))) _ at hn
    simpa only [neg_neg] using hn
  · rw [PolarIntegration.integral_polar _ hi] at hz
    have heq := setIntegral_congr_fun (μ := (volume : Measure ℝ)) measurableSet_Ioi he
    rw [heq, integral_neg] at hz
    exact neg_eq_zero.mp hz

theorem maxwell_weighted_flux (k : ℝ) (ε : Space → ℝ)
    (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r => weight a r * flux E H r) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi 0, weight a r * flux E H r) = 0 := by
  let χ := scaledCutoff a ha
  obtain ⟨hi,hz⟩ := MaterialPower.testMaxwell_power k ε hε M hb E H hE hH hMax
    χ.function χ.regular χ.compact
  exact weighted_flux a ha E H hi hz

theorem flux_eq_sphericalPower (k R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (ρ : Fin 3 → Space → ℂ) (E H : Field)
    (hE : ∀ x, R < ‖x‖ → E x = ExteriorContinuity.electric k ρ x)
    (hH : ∀ x, R < ‖x‖ → H x = MagneticResponse.magnetic k ρ x) :
    flux E H r = sphericalPower k r ρ := by
  apply integral_congr_ae
  filter_upwards with n
  have hn : R < ‖r • (n : Space)‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR hr),
      sphere_norm, mul_one] using hr
  rw [hE _ hn, hH _ hn]

theorem actual_flux_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (E H : Field)
    (hE : ∀ x, R < ‖x‖ → E x = ExteriorContinuity.electric k ρ x)
    (hH : ∀ x, R < ‖x‖ → H x = MagneticResponse.magnetic k ρ x) :
    Tendsto (flux E H) atTop (𝓝 (farPower k ρ)) := by
  apply (actual_spherical_power_limit k R hR ρ hρ hc).congr'
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (flux_eq_sphericalPower k R r hR hr ρ E H hE hH).symm

theorem nonnegative_limit_eq_zero (F : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlim : Tendsto F atTop (𝓝 L))
    (hw : ∀ a : ℝ, 0 < a →
      IntegrableOn (fun r => weight a r * F r) (Set.Ioi 0) ∧
        (∫ r in Set.Ioi 0, weight a r * F r) = 0) : L = 0 := by
  by_contra hn
  have hp : 0 < L := lt_of_le_of_ne hL (Ne.symm hn)
  have he : ∀ᶠ r in atTop, L/2 < F r :=
    hlim.eventually (eventually_gt_nhds (half_lt_self hp))
  obtain ⟨b,hb⟩ := eventually_atTop.mp he
  let a : ℝ := max b 1
  have ha : 0 < a := lt_of_lt_of_le (by norm_num) (le_max_right b 1)
  obtain ⟨hi,hz⟩ := hw a ha
  have hiw : IntegrableOn (weight a) (Set.Ioi 0) :=
    RadialWeight.scaledWeight_integrableOn a ha
  have hpos : 0 < ∫ r in Set.Ioi 0, weight a r :=
    RadialWeight.scaledWeight_integral_positive a ha
  have hle := integral_mono_ae (hiw.mul_const (L/2)) hi (show
      (fun r => weight a r * (L/2)) ≤ᵐ[volume.restrict (Set.Ioi 0)]
        (fun r => weight a r * F r) from by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    by_cases hra : r ≤ a
    · have hz : weight a r = 0 :=
        RadialWeight.scaledWeight_zero_inner a ha r hr.le hra
      simp only [hz, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left
        (hb r ((le_max_left b 1).trans (le_of_not_ge hra))).le
        (RadialWeight.scaledWeight_nonnegative a ha r hr))
  rw [integral_mul_const, hz] at hle
  exact (not_le_of_gt (mul_pos hpos (half_pos hp))) hle

theorem maxwell_farPower_zero (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M)
    (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (hextE : ∀ x, R < ‖x‖ → E x = ExteriorContinuity.electric k ρ x)
    (hextH : ∀ x, R < ‖x‖ → H x = MagneticResponse.magnetic k ρ x) :
    farPower k ρ = 0 :=
  nonnegative_limit_eq_zero (flux E H) (farPower k ρ) (farPower_nonnegative k ρ)
    (actual_flux_limit k R hR ρ hρ hc E H hextE hextH)
    (maxwell_weighted_flux k ε hε M hb E H hE hH hMax)

end OQ14.RadialFlux

#print axioms OQ14.RadialFlux.integrable_polar
#print axioms OQ14.RadialFlux.ray_testPower
#print axioms OQ14.RadialFlux.angular_testPower
#print axioms OQ14.RadialFlux.weighted_flux
#print axioms OQ14.RadialFlux.maxwell_weighted_flux
#print axioms OQ14.RadialFlux.flux_eq_sphericalPower
#print axioms OQ14.RadialFlux.actual_flux_limit
#print axioms OQ14.RadialFlux.nonnegative_limit_eq_zero
#print axioms OQ14.RadialFlux.maxwell_farPower_zero

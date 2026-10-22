import ConicalPotentialProjection
import ComplexPolarIntegration

/-! Genuine bounded-angular moments of actual L2 fields and their polar test pairings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.PolarMomentTesting
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
open scoped Topology

def moment (f : Space → ℂ) (σ : Sphere → ℂ) (r : ℝ) : ℂ :=
  ∫ n : Sphere, f (r • (n : Space))*σ n ∂angularMeasure

theorem angular_mul_memLp (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C) :
    MemLp (fun x => f x*σ (unit x)) 2 (volume : Measure Space) := by
  apply hf.of_le_mul (c := C) (hf.aestronglyMeasurable.mul (hσ.comp unit_measurable).aestronglyMeasurable)
  filter_upwards with x
  change ‖f x*σ (unit x)‖ ≤ C*‖f x‖
  rw [norm_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC (unit x)) (norm_nonneg _)

theorem weighted_spatial_integrable (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C)
    (η : ℝ → ℂ) (hη : Continuous η) (hc : HasCompactSupport η) :
    Integrable (fun x : Space => f x*σ (unit x)*η ‖x‖) := by
  have hp : MemLp (fun x : Space => η ‖x‖) 2 (volume : Measure Space) := (hη.comp continuous_norm).memLp_of_hasCompactSupport
    (RadialNormTest.radialNorm_compact η hc)
  exact (angular_mul_memLp f hf σ hσ C hC).integrable_mul hp

theorem integral_weighted_moment (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C)
    (η : ℝ → ℂ) (hη : Continuous η) (hc : HasCompactSupport η) :
    (∫ x : Space, f x*σ (unit x)*η ‖x‖)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*η r*moment f σ r := by
  rw [ComplexPolarIntegration.integral_polar_complex _ (weighted_spatial_integrable f hf σ hσ C hC η hη hc)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have he : (∫ n : Sphere, f (r • (n : Space))*σ (unit (r • (n : Space)))*η ‖r • (n : Space)‖ ∂angularMeasure)=
      η r*moment f σ r := by
    unfold moment
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    simp only [unit_polar r hr n,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos (show 0 < r from hr),mul_one,moment]
    ring
  change (r^2 : ℂ)*(∫ n : Sphere, f (r • (n : Space))*σ (unit (r • (n : Space)))*η ‖r • (n : Space)‖ ∂angularMeasure) = (r^2 : ℂ)*η r*moment f σ r
  rw [he,mul_assoc]

theorem integrable_weighted_moment (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C)
    (η : ℝ → ℂ) (hη : Continuous η) (hc : HasCompactSupport η) :
    IntegrableOn (fun r : ℝ => (r^2 : ℂ)*η r*moment f σ r) (Ioi (0 : ℝ)) := by
  have hi := ComplexPolarIntegration.integrable_radial_moment_complex _
    (weighted_spatial_integrable f hf σ hσ C hC η hη hc)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have he : (∫ n : Sphere, f (r • (n : Space))*σ (unit (r • (n : Space)))*η ‖r • (n : Space)‖ ∂angularMeasure)=
      η r*moment f σ r := by
    unfold moment
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    simp only [unit_polar r hr n,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos (show 0 < r from hr),mul_one,moment]
    ring
  rw [he,mul_assoc]

theorem weighted_moment_integrableOn (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C) (b : ℝ) :
    IntegrableOn (fun r : ℝ => (r^2 : ℂ)*moment f σ r) (Ioo (0 : ℝ) b) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨max b 1+1,max b 1+2,by linarith [le_max_right b (1 : ℝ)],by linarith⟩
  have hi : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(χ r : ℂ)*moment f σ r) (Ioo (0 : ℝ) b) := (integrable_weighted_moment f hf σ hσ C hC (fun r => (χ r : ℂ))
    (Complex.continuous_ofReal.comp χ.continuous) (χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp))).mono_set Ioo_subset_Ioi_self
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hχ : χ r=1 := χ.one_of_mem_closedBall (by
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_pos hr.1]
    dsimp only [χ]
    linarith [le_max_left b (1 : ℝ),hr.2])
  simp only [hχ,Complex.ofReal_one,mul_one]

theorem moment_integrableOn_annulus (f : Space → ℂ) (hf : MemLp f 2 (volume : Measure Space))
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C)
    (a b : ℝ) (ha : 0 < a) : IntegrableOn (moment f σ) (Ioo a b) := by
  have hi : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*moment f σ r) (Ioo a b) :=
    (weighted_moment_integrableOn f hf σ hσ C hC b).mono_set
      (fun r hr => ⟨ha.trans hr.1,hr.2⟩)
  have hm : AEStronglyMeasurable (fun r : ℝ => ((r^2 : ℝ) : ℂ)⁻¹) (volume.restrict (Ioo a b)) :=
    (Complex.measurable_ofReal.comp (measurable_id.pow_const 2)).inv.aestronglyMeasurable
  have hb : ∀ᵐ r : ℝ ∂volume.restrict (Ioo a b), ‖((r^2 : ℝ) : ℂ)⁻¹‖ ≤ (a^2)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
    have hs : a^2 ≤ r^2 := by nlinarith [ha.trans hr.1,hr.1]
    simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos ha) hs
  apply (hi.bdd_mul' hm hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hr0 : r≠0 := (ha.trans hr.1).ne'
  simp only [Complex.ofReal_pow,inv_mul_cancel_left₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr0))]

end OQ14.PolarMomentTesting

#print axioms OQ14.PolarMomentTesting.angular_mul_memLp
#print axioms OQ14.PolarMomentTesting.weighted_spatial_integrable
#print axioms OQ14.PolarMomentTesting.integral_weighted_moment
#print axioms OQ14.PolarMomentTesting.integrable_weighted_moment
#print axioms OQ14.PolarMomentTesting.weighted_moment_integrableOn
#print axioms OQ14.PolarMomentTesting.moment_integrableOn_annulus

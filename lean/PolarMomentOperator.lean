import PolarMomentAE

/-! Bounded linear physical spherical-moment map into radial L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.PolarMomentOperator
open MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.PolarMomentEnergy OQ14.PolarMomentTesting
open scoped Topology ComplexConjugate

abbrev RadialL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

def momentL2 (σ : Sphere → ℂ) (hσm : Measurable σ) (hσ : MemLp σ 2 angularMeasure)
    (f : ScalarL2) : RadialL2 :=
  (radial_moment_memLp f σ hσm hσ).toLp (fun r : ℝ => (r : ℂ) * moment f σ r)

theorem momentL2_actual (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (f : ScalarL2) :
    (momentL2 σ hσm hσ f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => (r : ℂ) * moment f σ r :=
  (radial_moment_memLp f σ hσm hσ).coeFn_toLp

theorem momentL2_add (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (f g : ScalarL2) :
    momentL2 σ hσm hσ (f + g) = momentL2 σ hσm hσ f + momentL2 σ hσm hσ g := by
  apply Lp.ext
  have he := PolarMomentAE.moment_congr (Lp.coeFn_add f g) σ
  filter_upwards [momentL2_actual σ hσm hσ (f+g), momentL2_actual σ hσm hσ f,
    momentL2_actual σ hσm hσ g, Lp.coeFn_add (momentL2 σ hσm hσ f) (momentL2 σ hσm hσ g),
    PolarMomentAE.moment_add f g σ hσ, he] with r hfg hf hg ha hm he
  rw [hfg, ha, Pi.add_apply, hf, hg, he, hm, mul_add]

theorem momentL2_smul (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (a : ℂ) (f : ScalarL2) :
    momentL2 σ hσm hσ (a • f) = a • momentL2 σ hσm hσ f := by
  apply Lp.ext
  have hm := PolarMomentAE.moment_congr (Lp.coeFn_smul a f) σ
  filter_upwards [momentL2_actual σ hσm hσ (a • f), momentL2_actual σ hσm hσ f,
    Lp.coeFn_smul a (momentL2 σ hσm hσ f), hm] with r haf hf ha hm
  rw [haf, ha, Pi.smul_apply, hf, hm]
  simp only [moment, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem momentL2_energy (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (f : ScalarL2) :
    ‖momentL2 σ hσm hσ f‖ ^ 2 ≤ weightNorm σ hσ * ‖f‖ ^ 2 := by
  have hf : Integrable (fun x : Space => ‖f x‖^2) := (Lp.memLp f).norm.integrable_sq
  have hr : IntegrableOn
      (fun r : ℝ => r^2 * ∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) (Ioi 0) := by
    simpa only [smul_eq_mul] using ComplexPolarIntegration.integrable_radial_moment _ hf
  have hm := (Lp.memLp (momentL2 σ hσm hσ f)).norm.integrable_sq
  have hb : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖momentL2 σ hσm hσ f r‖^2 ≤ weightNorm σ hσ *
        (r^2 * ∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) := by
    filter_upwards [momentL2_actual σ hσm hσ f, slice_memLp_ae f] with r he hs
    rw [he, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left (moment_norm_sq_le _ σ hs hσ) (sq_nonneg r)).trans_eq (by ring)
  rw [L2Parametric.norm_sq_integral, L2Parametric.norm_sq_integral]
  calc
    _ ≤ ∫ r in Ioi (0 : ℝ), weightNorm σ hσ *
        (r^2 * ∫ ω : Sphere, ‖f (r • (ω : Space))‖^2 ∂angularMeasure) :=
      integral_mono_ae hm (hr.const_mul _) hb
    _ = _ := by
      rw [integral_const_mul]
      have he := ComplexPolarIntegration.integral_polar (fun x : Space => ‖f x‖^2) hf
      simp only [smul_eq_mul] at he
      rw [← he]

theorem momentL2_bound (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (f : ScalarL2) :
    ‖momentL2 σ hσm hσ f‖ ≤ Real.sqrt (weightNorm σ hσ) * ‖f‖ := by
  have hw : 0 ≤ weightNorm σ hσ := sq_nonneg _
  have hs := Real.sq_sqrt hw
  have hb := momentL2_energy σ hσm hσ f
  have hp : 0 ≤ Real.sqrt (weightNorm σ hσ) * ‖f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg (‖momentL2 σ hσm hσ f‖ - Real.sqrt (weightNorm σ hσ) * ‖f‖)]

def momentLinear (σ : Sphere → ℂ) (hσm : Measurable σ) (hσ : MemLp σ 2 angularMeasure) :
    ScalarL2 →ₗ[ℂ] RadialL2 where
  toFun := momentL2 σ hσm hσ
  map_add' := momentL2_add σ hσm hσ
  map_smul' := momentL2_smul σ hσm hσ

def operator (σ : Sphere → ℂ) (hσm : Measurable σ) (hσ : MemLp σ 2 angularMeasure) :
    ScalarL2 →L[ℂ] RadialL2 :=
  (momentLinear σ hσm hσ).mkContinuous (Real.sqrt (weightNorm σ hσ))
    (momentL2_bound σ hσm hσ)

theorem operator_actual (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) (f : ScalarL2) :
    (operator σ hσm hσ f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => (r : ℂ) * moment f σ r := momentL2_actual σ hσm hσ f

end OQ14.PolarMomentOperator
#print axioms OQ14.PolarMomentOperator.momentL2_energy
#print axioms OQ14.PolarMomentOperator.momentL2_bound
#print axioms OQ14.PolarMomentOperator.operator_actual

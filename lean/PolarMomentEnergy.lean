import PolarMomentTesting
import L2Parametric

/-! Actual weighted radial L2 energy of bounded-angular projections. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.PolarMomentEnergy
open MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarIntegration OQ14.PolarMomentTesting
open scoped Topology InnerProductSpace ComplexConjugate

abbrev ScalarL2 := Lp ℂ 2 (volume : Measure Space)

theorem slice_memLp_ae (f : ScalarL2) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), MemLp (fun n : Sphere => f (r • (n : Space))) 2 angularMeasure := by
  have hf2 : Integrable (fun x : Space => ‖f x‖^2) := (Lp.memLp f).norm.integrable_sq
  have hp := (ComplexPolarIntegration.integrable_polar_product _ hf2).prod_left_ae
  have hs : ∀ᵐ r : Radius ∂radialMeasure, MemLp (fun n : Sphere => f ((r : ℝ) • (n : Space))) 2 angularMeasure := by
    filter_upwards [hp] with r hr
    have hm : StronglyMeasurable (fun n : Sphere => f ((r : ℝ) • (n : Space))) :=
      (Lp.stronglyMeasurable f).comp_measurable (continuous_const.smul continuous_subtype_val).measurable
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hr
  have hd : Measurable (fun r : Radius => ENNReal.ofReal ((r : ℝ)^2)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2)
  have hb : ∀ᵐ r : Radius ∂(volume.comap ((↑) : Radius → ℝ)),
      MemLp (fun n : Sphere => f ((r : ℝ) • (n : Space))) 2 angularMeasure := by
    have hh := (ae_withDensity_iff hd).mp hs
    filter_upwards [hh] with r hr
    exact hr (ENNReal.ofReal_pos.mpr (sq_pos_of_pos r.property)).ne'
  exact (ae_restrict_iff_subtype measurableSet_Ioi).mpr hb

theorem moment_stronglyMeasurable (f : ScalarL2) (σ : Sphere → ℂ) (hσ : Measurable σ) :
    StronglyMeasurable (moment f σ) := by
  have hp : StronglyMeasurable (fun p : ℝ × Sphere => f (p.1 • (p.2 : Space))*σ p.2) :=
    ((Lp.stronglyMeasurable f).comp_measurable
      (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).measurable).mul
      (hσ.stronglyMeasurable.comp_measurable measurable_snd)
  exact hp.integral_prod_right'

def weightNorm (σ : Sphere → ℂ) (hσ : MemLp σ 2 angularMeasure) : ℝ :=
  ‖((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hσ).toLp (fun n => conj (σ n))‖^2

theorem moment_norm_sq_le (g σ : Sphere → ℂ) (hg : MemLp g 2 angularMeasure) (hσ : MemLp σ 2 angularMeasure) :
    ‖∫ n : Sphere, g n*σ n ∂angularMeasure‖^2 ≤ weightNorm σ hσ*(∫ n : Sphere, ‖g n‖^2 ∂angularMeasure) := by
  let G : Lp ℂ 2 angularMeasure := hg.toLp g
  have hc : MemLp (fun n => conj (σ n)) 2 angularMeasure := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_memLp' hσ
  let S : Lp ℂ 2 angularMeasure := hc.toLp (fun n => conj (σ n))
  have he : ⟪S,G⟫_ℂ=∫ n : Sphere, g n*σ n ∂angularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp,hg.coeFn_toLp] with n hs hg
    change ⟪S n,G n⟫_ℂ=_
    change S n=conj (σ n) at hs
    change G n=g n at hg
    simp [RCLike.inner_apply,hs,hg,mul_comm]
  have hn : ‖G‖^2=∫ n : Sphere, ‖g n‖^2 ∂angularMeasure := by
    rw [L2Parametric.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with n hn
    rw [show G n=g n from hn]
  have hbound := norm_inner_le_norm (𝕜 := ℂ) S G
  rw [he] at hbound
  calc
    _ ≤ (‖S‖*‖G‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := by rw [mul_pow,hn]; rfl

theorem radial_moment_memLp (f : ScalarL2) (σ : Sphere → ℂ) (hσm : Measurable σ)
    (hσ : MemLp σ 2 angularMeasure) :
    MemLp (fun r : ℝ => (r : ℂ)*moment f σ r) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : AEStronglyMeasurable (fun r : ℝ => (r : ℂ)*moment f σ r)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.continuous_ofReal.stronglyMeasurable.mul (moment_stronglyMeasurable f σ hσm)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hEnergy := ComplexPolarIntegration.integrable_radial_moment (fun x : Space => ‖f x‖^2)
    ((Lp.memLp f).norm.integrable_sq)
  have he : IntegrableOn (fun r : ℝ => r^2*(∫ n : Sphere, ‖f (r • (n : Space))‖^2 ∂angularMeasure)) (Ioi (0 : ℝ)) := by
    simpa only [smul_eq_mul] using hEnergy
  apply (he.const_mul (weightNorm σ hσ)).mono' (hm.norm.pow 2)
  filter_upwards [slice_memLp_ae f] with r hr
  have hb := moment_norm_sq_le _ σ hr hσ
  change ‖‖(r : ℂ)*moment f σ r‖^2‖ ≤ weightNorm σ hσ*(r^2*(∫ n : Sphere, ‖f (r • (n : Space))‖^2 ∂angularMeasure))
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg r)).trans_eq (by ring)

end OQ14.PolarMomentEnergy

#print axioms OQ14.PolarMomentEnergy.slice_memLp_ae
#print axioms OQ14.PolarMomentEnergy.moment_stronglyMeasurable
#print axioms OQ14.PolarMomentEnergy.moment_norm_sq_le
#print axioms OQ14.PolarMomentEnergy.radial_moment_memLp

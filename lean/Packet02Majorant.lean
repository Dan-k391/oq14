import Packet02Surface
import SphereAngularSymmetry

/-! Reduction of the fixed-sphere source estimate to the angular kernel. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet02Majorant
open MeasureTheory OQ14.Maxwell OQ14.AngularPower

def kernel (r : ℝ) (ω : Sphere) (y : Space) : ℝ := (‖r • (ω : Space) - y‖⁻¹)^2

def angular (r : ℝ) (y : Space) : ℝ := ∫ ω : Sphere, kernel r ω y ∂angularMeasure

theorem angular_isometry (r : ℝ) (y : Space) (L : Space ≃ₗᵢ[ℝ] Space) :
    angular r (L y) = angular r y := by
  unfold angular
  rw [← SphereAngularSymmetry.integral_sphereMap L (fun ω => kernel r ω (L y))]
  apply integral_congr_ae
  filter_upwards with ω
  unfold kernel
  change (‖r • L (ω : Space) - L y‖⁻¹)^2 = (‖r • (ω : Space) - y‖⁻¹)^2
  rw [← map_smul, ← map_sub, L.norm_map]
theorem angular_radial (r : ℝ) (y w : Space) (h : ‖y‖ = ‖w‖) :
    angular r y = angular r w := by
  let L : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (y - w))ᗮ.reflection
  have hw : L y = w := Submodule.reflection_sub h
  rw [← hw, angular_isometry]
theorem kernel_nonneg (r : ℝ) (ω : Sphere) (y : Space) : 0 ≤ kernel r ω y := sq_nonneg _

theorem kernel_measurable (r : ℝ) : Measurable (fun p : Sphere × Space => kernel r p.1 p.2) := by
  unfold kernel
  fun_prop

theorem slice_integrable_of_norm_ne (r : ℝ) (y : Space) (hy : ‖y‖ ≠ |r|) :
    Integrable (fun ω : Sphere => kernel r ω y) angularMeasure := by
  have hn : ∀ ω : Sphere, ‖r • (ω : Space) - y‖ ≠ 0 := by
    intro ω hz
    have hzero : r • (ω : Space) - y = 0 := norm_eq_zero.mp hz
    have heq : r • (ω : Space) = y := sub_eq_zero.mp hzero
    have hnorm := congrArg norm heq
    simp only [norm_smul, Real.norm_eq_abs, sphere_norm, mul_one] at hnorm
    exact hy hnorm.symm
  have hc : Continuous (fun ω : Sphere => ‖r • (ω : Space) - y‖) := by
    fun_prop
  have hk : Continuous (fun ω : Sphere => kernel r ω y) := (hc.inv₀ hn).pow 2
  exact hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem slice_integrable_ae (r : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), Integrable (fun ω : Sphere => kernel r ω y) angularMeasure := by
  have h : ∀ᵐ y ∂(volume : Measure Space), ‖y‖ ≠ |r| := by
    rw [ae_iff]
    have hs : {y : Space | ¬ ‖y‖ ≠ |r|} = Metric.sphere 0 |r| := by
      ext y
      simp only [Set.mem_setOf_eq, not_not, Metric.mem_sphere, dist_zero_right]
    rw [hs]
    exact Measure.addHaar_sphere (volume : Measure Space) 0 |r|
  exact h.mono (slice_integrable_of_norm_ne r)
theorem joint_integrable (r : ℝ) (f : Space → ℝ)
    (hf : MemLp f 2 volume)
    (hslice : ∀ᵐ y ∂(volume : Measure Space), Integrable (fun ω : Sphere => kernel r ω y) angularMeasure)
    (hangular : MemLp (angular r) 2 volume) :
    Integrable (fun p : Sphere × Space => f p.2 * kernel r p.1 p.2)
      (angularMeasure.prod volume) := by
  have hm : AEStronglyMeasurable (fun p : Sphere × Space => f p.2 * kernel r p.1 p.2)
      (angularMeasure.prod volume) :=
    hf.aestronglyMeasurable.snd.mul
      (kernel_measurable r).aestronglyMeasurable
  apply (integrable_prod_iff' hm).2
  constructor
  · filter_upwards [hslice] with y hy
    exact hy.const_mul (f y)
  · have hi : Integrable (fun y => ‖f y‖ * angular r y) volume := by
      exact hf.norm.integrable_mul hangular
    convert hi using 1
    funext y
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg r _ _),
      integral_const_mul, angular]

theorem joint_complex_integrable (r : ℝ) (f : Space → ℂ)
    (hf : MemLp f 2 volume) (hangular : MemLp (angular r) 2 volume) :
    Integrable (fun p : Sphere × Space => f p.2 * ((kernel r p.1 p.2 : ℝ) : ℂ))
      (angularMeasure.prod volume) := by
  have hb := joint_integrable r (fun y => ‖f y‖) hf.norm (slice_integrable_ae r) hangular
  apply hb.mono'
  · exact hf.aestronglyMeasurable.snd.mul
      (Complex.measurable_ofReal.comp (kernel_measurable r)).aestronglyMeasurable
  · filter_upwards with p
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (kernel_nonneg r p.1 p.2), le_refl]
theorem good_ae_of_angular_memLp (r : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ l, MemLp (ρ l) 2 volume) (hρm : ∀ l, Measurable (ρ l))
    (hangular : MemLp (angular r) 2 volume) :
    ∀ᵐ ω ∂angularMeasure, ∀ l,
      Integrable (fun y => ρ l y * ((kernel r ω y : ℝ) : ℂ)) volume := by
  have hjoint (l : Fin 3) : Integrable
      (fun p : Sphere × Space => ρ l p.2 * ((kernel r p.1 p.2 : ℝ) : ℂ))
      (angularMeasure.prod volume) := by
    have hb := joint_integrable r (fun y => ‖ρ l y‖) (hρ l).norm
      (slice_integrable_ae r) hangular
    apply hb.mono'
    · exact (((hρm l).comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (kernel_measurable r))).aestronglyMeasurable
    · filter_upwards with p
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (kernel_nonneg r p.1 p.2), le_refl]
  exact ae_all_iff.mpr (fun l => (hjoint l).prod_right_ae)
theorem good_ae_of_angular_memLp' (r : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ l, MemLp (ρ l) 2 volume)
    (hangular : MemLp (angular r) 2 volume) :
    ∀ᵐ ω ∂angularMeasure, ∀ l,
      Integrable (fun y => ρ l y * ((kernel r ω y : ℝ) : ℂ)) volume := by
  let ρ' : Fin 3 → Space → ℂ := fun l => (hρ l).aestronglyMeasurable.mk (ρ l)
  have heq (l : Fin 3) : ρ l =ᵐ[volume] ρ' l := (hρ l).aestronglyMeasurable.ae_eq_mk
  have hρ' (l : Fin 3) : MemLp (ρ' l) 2 volume := (memLp_congr_ae (heq l)).mp (hρ l)
  have hm (l : Fin 3) : Measurable (ρ' l) := (hρ l).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  filter_upwards [good_ae_of_angular_memLp r ρ' hρ' hm hangular] with ω hω
  intro l
  apply (hω l).congr
  filter_upwards [(heq l).symm] with y hy
  rw [hy]
end OQ14.Packet02Majorant
#print axioms OQ14.Packet02Majorant.joint_integrable

#print axioms OQ14.Packet02Majorant.slice_integrable_ae

#print axioms OQ14.Packet02Majorant.good_ae_of_angular_memLp

#print axioms OQ14.Packet02Majorant.good_ae_of_angular_memLp'

#print axioms OQ14.Packet02Majorant.angular_isometry

#print axioms OQ14.Packet02Majorant.angular_radial

#print axioms OQ14.Packet02Majorant.kernel_nonneg
#print axioms OQ14.Packet02Majorant.kernel_measurable
#print axioms OQ14.Packet02Majorant.slice_integrable_of_norm_ne
#print axioms OQ14.Packet02Majorant.joint_complex_integrable

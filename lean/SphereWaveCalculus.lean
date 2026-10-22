import SphereWaveTransform
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual derivatives under the finite sphere integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereWaveCalculus
open MeasureTheory Metric Set SphereReactionKernel
open scoped InnerProductSpace Topology

def phase (k : ℝ) (θ : Sphere) : Space →L[ℝ] ℂ :=
  (innerSL ℝ θ.val).smulRight (Complex.I*(k : ℂ))

theorem phase_apply (k : ℝ) (θ : Sphere) (x : Space) :
    phase k θ x = ((k*⟪θ.val,x⟫_ℝ : ℝ) : ℂ)*Complex.I := by
  simp [phase, smul_eq_mul]
  ring

theorem phase_bound (k : ℝ) (θ : Sphere) : ‖phase k θ‖ ≤ |k| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg k)
  intro x
  rw [phase_apply, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [sphere_norm, one_mul] using abs_real_inner_le_norm θ.val x)
    (abs_nonneg k)

theorem phase_continuous (k : ℝ) : Continuous (phase k) := by
  exact (ContinuousLinearMap.smulRightL ℝ Space ℂ).continuous₂.comp₂
    ((innerSL ℝ).continuous.comp continuous_subtype_val) continuous_const

theorem wave_hasFDerivAt (k : ℝ) (θ : Sphere) (x : Space) :
    HasFDerivAt (fun y => wave k y θ) (wave k x θ • phase k θ) x := by
  simpa only [phase_apply, wave] using (phase k θ).hasFDerivAt.cexp

def moment (a : Sphere → ℂ) (k : ℝ) (x : Space) : ℂ :=
  ∫ θ : Sphere, a θ*wave k x θ ∂surface

theorem moment_integrable (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ)
    (hA : ∀ θ, ‖a θ‖ ≤ A) (k : ℝ) (x : Space) :
    Integrable (fun θ : Sphere => a θ*wave k x θ) surface := by
  apply (integrable_const A).mono' (ha.aestronglyMeasurable.mul (SphereWaveTransform.wave_integrable k x).aestronglyMeasurable)
  filter_upwards with θ
  simpa only [Pi.mul_apply, norm_mul, wave_norm, mul_one] using hA θ

theorem moment_hasFDerivAt (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ)
    (hA : ∀ θ, ‖a θ‖ ≤ A) (k : ℝ) (x : Space) :
    HasFDerivAt (moment a k)
      (∫ θ : Sphere, (a θ*wave k x θ) • phase k θ ∂surface) x := by
  unfold moment
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y θ => a θ*wave k y θ)
    (F' := fun y θ => (a θ*wave k y θ) • phase k θ) (ε := 1) (bound := fun _ => A*|k|) (by norm_num)
  · filter_upwards with y
    exact (moment_integrable a ha A hA k y).aestronglyMeasurable
  · exact moment_integrable a ha A hA k x
  · apply Continuous.aestronglyMeasurable
    exact (ha.mul (by unfold wave; fun_prop)).smul (phase_continuous k)
  · filter_upwards with θ y _
    apply ((phase k θ).opNorm_smul_le (a θ*wave k y θ)).trans
    rw [norm_mul, wave_norm, mul_one]
    exact mul_le_mul (hA θ) (phase_bound k θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))
  · exact integrable_const _
  · filter_upwards with θ y _
    simpa only [smul_smul, smul_eq_mul] using (wave_hasFDerivAt k θ y).const_mul (a θ)

theorem moment_partial (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ)
    (hA : ∀ θ, ‖a θ‖ ≤ A) (k : ℝ) (x : Space) (i : Fin 3) :
    Maxwell.dcoord (moment a k) x i = (Complex.I*(k : ℂ))*
      moment (fun θ => a θ*(θ.val i : ℂ)) k x := by
  have hm : Continuous (fun θ : Sphere => (a θ*wave k x θ) • phase k θ) :=
    (ha.mul (by unfold wave; fun_prop)).smul (phase_continuous k)
  have hi : Integrable (fun θ : Sphere => (a θ*wave k x θ) • phase k θ) surface := by
    apply (integrable_const (A*|k|)).mono' hm.aestronglyMeasurable
    filter_upwards with θ
    apply ((phase k θ).opNorm_smul_le (a θ*wave k x θ)).trans
    rw [norm_mul, wave_norm, mul_one]
    exact mul_le_mul (hA θ) (phase_bound k θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))
  rw [Maxwell.dcoord, (moment_hasFDerivAt a ha A hA k x).fderiv,
    ContinuousLinearMap.integral_apply hi]
  unfold moment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  simp [ContinuousLinearMap.smul_apply, phase, Maxwell.basis,
    EuclideanSpace.inner_single_right, smul_eq_mul]
  ring

def coordinate (i : Fin 3) (θ : Sphere) : ℂ := θ.val i

theorem coordinate_continuous (i : Fin 3) : Continuous (coordinate i) := by
  exact Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)

theorem coordinate_bound (i : Fin 3) (θ : Sphere) : ‖coordinate i θ‖ ≤ 1 := by
  simpa only [coordinate, Complex.norm_real, sphere_norm] using PiLp.norm_apply_le θ.val i
end OQ14.SphereWaveCalculus
#print axioms OQ14.SphereWaveCalculus.phase_apply
#print axioms OQ14.SphereWaveCalculus.phase_bound
#print axioms OQ14.SphereWaveCalculus.phase_continuous
#print axioms OQ14.SphereWaveCalculus.wave_hasFDerivAt
#print axioms OQ14.SphereWaveCalculus.moment_integrable
#print axioms OQ14.SphereWaveCalculus.moment_hasFDerivAt




#print axioms OQ14.SphereWaveCalculus.moment_partial
#print axioms OQ14.SphereWaveCalculus.coordinate_continuous
#print axioms OQ14.SphereWaveCalculus.coordinate_bound

import ScalarRadiation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Actual exterior derivatives of the scalar source response -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarExterior

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
  OQ14.ScalarRadiation Filter
open scoped Topology

def coordinateCLM (j : Fin 3) : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj j)

theorem coordinateCLM_apply (j : Fin 3) (x : Space) :
    coordinateCLM j x = (x j : ℂ) := rfl

theorem coordinateCLM_norm_le (j : Fin 3) : ‖coordinateCLM j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [coordinateCLM_apply, Complex.norm_real, one_mul] using PiLp.norm_apply_le x j

def gradientCLM (k : ℝ) (x : Space) : Space →L[ℝ] ℂ :=
  ∑ j : Fin 3, phiGradient k x j • coordinateCLM j

theorem gradientCLM_basis (k : ℝ) (x : Space) (j : Fin 3) :
    gradientCLM k x (basis j) = phiGradient k x j := by
  simp [gradientCLM, coordinateCLM_apply, basis, EuclideanSpace.single_apply, apply_ite]

theorem gradientCLM_measurable (k : ℝ) : Measurable (gradientCLM k) := by
  unfold gradientCLM
  exact Finset.measurable_sum _ (fun j _ => (KernelGradient.gradient_measurable k j).smul measurable_const)

theorem gradientCLM_norm_le (k : ℝ) (x : Space) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ j, ‖phiGradient k x j‖ ≤ B) : ‖gradientCLM k x‖ ≤ 3 * B := by
  calc
    _ ≤ ∑ j : Fin 3, ‖phiGradient k x j • coordinateCLM j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, B := by
      apply Finset.sum_le_sum
      intro j _
      rw [_root_.norm_smul (phiGradient k x j) (coordinateCLM j)]
      exact (mul_le_mul_of_nonneg_left (coordinateCLM_norm_le j) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hb j)
    _ = _ := by simp

theorem phi_hasFDerivAt (k : ℝ) (x : Space) (hx : x ≠ 0) :
    HasFDerivAt (phi k) (gradientCLM k x) x := by
  have hd := ((phi_contDiffAt k x hx).differentiableAt (by simp)).hasFDerivAt
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ j : Fin 3, v j • basis j) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, basis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  rw [← hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_smul, gradientCLM_basis]
  exact congrArg (fun z : ℂ => v j • z) (phi_partial k x hx j).symm

theorem exterior_separation (R : ℝ) (x : Space) (_hx : R < ‖x‖)
    (z y : Space) (hz : z ∈ ball x ((‖x‖ - R) / 2)) (hy : y ∈ closedBall 0 R) :
    (‖x‖ - R) / 2 ≤ ‖z-y‖ := by
  have hz' : ‖x-z‖ < (‖x‖ - R) / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
  have h1 := norm_sub_norm_le x z
  have h2 := norm_sub_norm_le z y
  linarith

theorem gradient_bound_of_separation (k : ℝ) (x : Space) {a : ℝ} (ha : 0 < a)
    (hx : a ≤ ‖x‖) :
    ‖gradientCLM k x‖ ≤ 3 * ((4 * Real.pi)⁻¹ * (|k| * a⁻¹ + (a⁻¹)^2)) := by
  apply gradientCLM_norm_le _ _ (by positivity)
  intro j
  apply (KernelGradient.gradient_bound k x j).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := one_div_le_one_div_of_le ha hx
  simp only [one_div] at h
  exact add_le_add (mul_le_mul_of_nonneg_left h (abs_nonneg _))
    (pow_le_pow_left₀ (by positivity) h 2)

def responseDerivative (k : ℝ) (ρ : Space → ℂ) (x : Space) : Space →L[ℝ] ℂ :=
  ∫ y, ρ y • gradientCLM k (x-y)

theorem response_derivative_integrable (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (x : Space) (hx : R < ‖x‖) :
    Integrable (fun y => ρ y • gradientCLM k (x-y)) := by
  let a := (‖x‖ - R) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let B := 3 * ((4 * Real.pi)⁻¹ * (|k| * a⁻¹ + (a⁻¹)^2))
  apply (hρ.norm.mul_const B).mono'
    (hρ.aestronglyMeasurable.smul
      ((gradientCLM_measurable k).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  filter_upwards with y
  by_cases hy : ρ y = 0
  · change ‖ρ y • gradientCLM k (x-y)‖ ≤ ‖ρ y‖ * B
    rw [_root_.norm_smul (ρ y) (gradientCLM k (x-y)), hy]
    simp
  · have hys : y ∈ closedBall 0 R :=
      Classical.byContradiction (fun hn => hy (hc y hn))
    change ‖ρ y • gradientCLM k (x-y)‖ ≤ ‖ρ y‖ * B
    rw [_root_.norm_smul (ρ y) (gradientCLM k (x-y))]
    exact mul_le_mul_of_nonneg_left
      (gradient_bound_of_separation k (x-y) ha
        (exterior_separation R x hx x y (mem_ball_self ha) hys)) (norm_nonneg _)

theorem response_hasFDerivAt (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (x : Space) (hx : R < ‖x‖) :
    HasFDerivAt (response (phi k) ρ) (responseDerivative k ρ x) x := by
  let a := (‖x‖ - R) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let B := 3 * ((4 * Real.pi)⁻¹ * (|k| * a⁻¹ + (a⁻¹)^2))
  have hys (y : Space) (hy : ρ y ≠ 0) : y ∈ closedBall 0 R := by
    by_contra hn
    exact hy (hc y hn)
  have hsep (z y : Space) (hz : z ∈ ball x a) (hy : ρ y ≠ 0) :
      a ≤ ‖z-y‖ := exterior_separation R x hx z y hz (hys y hy)
  have hi : Integrable (fun y => ρ y * phi k (x-y)) := by
    apply source_integrand_integrable (phi k) ρ (KernelIntegrability.phi_measurable k) hρ x
      ((4 * Real.pi)⁻¹ * a⁻¹)
    intro y hy
    rw [KernelIntegrability.phi_norm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [one_div] using one_div_le_one_div_of_le ha (hsep x y (mem_ball_self ha) hy)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => ρ y * phi k (z-y))
    (F' := fun z y => ρ y • gradientCLM k (z-y))
    (bound := fun y => ‖ρ y‖ * B) ha
  · exact Eventually.of_forall (fun z => hρ.aestronglyMeasurable.mul
      ((KernelIntegrability.phi_measurable k).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · exact hi
  · exact (response_derivative_integrable k R ρ hρ hc x hx).aestronglyMeasurable
  · filter_upwards with y
    intro z hz
    by_cases hy : ρ y = 0
    · rw [_root_.norm_smul (ρ y) (gradientCLM k (z-y)), hy]
      simp
    · rw [_root_.norm_smul (ρ y) (gradientCLM k (z-y))]
      exact mul_le_mul_of_nonneg_left
        (gradient_bound_of_separation k (z-y) ha (hsep z y hz hy)) (norm_nonneg _)
  · exact hρ.norm.mul_const B
  · filter_upwards with y
    intro z hz
    by_cases hy : ρ y = 0
    · simp only [hy, zero_mul]
      have hz0 : (0 : ℂ) • gradientCLM k (z-y) = (0 : Space →L[ℝ] ℂ) :=
        _root_.zero_smul ℂ (gradientCLM k (z-y))
      rw [hz0]
      exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z
    · have hzy : z-y ≠ 0 := norm_pos_iff.mp (ha.trans_le (hsep z y hz hy))
      have hd := (phi_hasFDerivAt k (z-y) hzy).comp z ((hasFDerivAt_id z).sub_const y)
      simpa only [ContinuousLinearMap.comp_id] using hd.const_mul (ρ y)

theorem response_partial (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    dcoord (response (phi k) ρ) x i = response (fun z => phiGradient k z i) ρ x := by
  unfold dcoord
  rw [(response_hasFDerivAt k R ρ hρ hc x hx).fderiv]
  unfold responseDerivative
  rw [ContinuousLinearMap.integral_apply (response_derivative_integrable k R ρ hρ hc x hx)]
  simp only [ContinuousLinearMap.smul_apply, gradientCLM_basis, smul_eq_mul, response]

theorem response_sommerfeld_limit (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0)
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) (i : Fin 3) :
    Tendsto (fun t => (‖γ t‖ : ℂ) *
      (dcoord (response (phi k) ρ) (γ t) i -
        Complex.I * (k : ℂ) * unitCoordinate i (γ t) * response (phi k) ρ (γ t)))
      atTop (𝓝 0) := by
  apply (response_outgoing_limit k R hR ρ hρ hc γ hγ i).congr'
  filter_upwards [hγ.eventually (eventually_gt_atTop R)] with t ht
  rw [response_partial k R ρ hρ hc (γ t) ht i]

end OQ14.ScalarExterior

#print axioms OQ14.ScalarExterior.gradientCLM_basis
#print axioms OQ14.ScalarExterior.gradientCLM_measurable
#print axioms OQ14.ScalarExterior.gradientCLM_norm_le
#print axioms OQ14.ScalarExterior.phi_hasFDerivAt
#print axioms OQ14.ScalarExterior.exterior_separation
#print axioms OQ14.ScalarExterior.gradient_bound_of_separation
#print axioms OQ14.ScalarExterior.response_derivative_integrable
#print axioms OQ14.ScalarExterior.response_hasFDerivAt
#print axioms OQ14.ScalarExterior.response_partial
#print axioms OQ14.ScalarExterior.response_sommerfeld_limit

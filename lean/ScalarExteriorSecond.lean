import ScalarExterior
import NewtonExteriorResponse

/-! # Actual second derivatives of the exterior scalar response -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarExteriorSecond

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
  OQ14.ScalarExterior Filter
open scoped Topology

/-- Compact support and a positive exterior gap give a common derivative
bound on an actual neighborhood of the observation point. -/
theorem derivative_source_bound (L : Space → Space →L[ℝ] ℂ)
    (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (R : ℝ) (x : Space) (hx : R < ‖x‖) :
    ∃ a B : ℝ, 0 < a ∧
      (∀ z ∈ ball x a, ∀ y ∈ closedBall 0 R, z-y ≠ 0 ∧ ‖L (z-y)‖ ≤ B) := by
  let a := (‖x‖-R)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hn (z y : Space) (hz : z ∈ closedBall x a) (hy : y ∈ closedBall 0 R) :
      z-y ≠ 0 := by
    have hd : ‖x-z‖ ≤ a := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have hyr : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    have h1 := norm_sub_norm_le x z
    have h2 := norm_sub_norm_le z y
    apply norm_pos_iff.mp
    dsimp [a] at hd
    linarith
  have hK := (isCompact_closedBall x a).prod (isCompact_closedBall (0 : Space) R)
  have hcont : ContinuousOn (fun p : Space × Space => L (p.1-p.2))
      (closedBall x a ×ˢ closedBall 0 R) := by
    intro p hp
    exact ((hL (p.1-p.2) (hn _ _ hp.1 hp.2)).comp
      (f := fun q : Space × Space => q.1-q.2)
      (continuous_fst.sub continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨a, B, ha, fun z hz y hy =>
    ⟨hn z y (ball_subset_closedBall hz) hy, hB (z,y) ⟨ball_subset_closedBall hz, hy⟩⟩⟩

/-- Ordinary differentiation under the actual source integral for a kernel
whose actual derivative is continuous away from the source point. -/
theorem response_derivative_off_source (q : Space → ℂ) (L : Space → Space →L[ℝ] ℂ)
    (hq : Measurable q) (hLm : Measurable L)
    (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (hd : ∀ z, z ≠ 0 → HasFDerivAt q (L z) z)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    Integrable (fun y => ρ y • L (x-y)) ∧
      HasFDerivAt (response q ρ) (∫ y, ρ y • L (x-y)) x := by
  obtain ⟨a, B, ha, hB⟩ := derivative_source_bound L hL R x hx
  have hys (y : Space) (hy : ρ y ≠ 0) : y ∈ closedBall 0 R :=
    Classical.byContradiction (fun hn => hy (hc y hn))
  have hm (z : Space) : AEStronglyMeasurable (fun y => ρ y • L (z-y)) :=
    hρ.aestronglyMeasurable.smul
      (hLm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hb (y z : Space) (hz : z ∈ ball x a) :
      ‖ρ y • L (z-y)‖ ≤ ‖ρ y‖ * B := by
    rw [_root_.norm_smul (ρ y) (L (z-y))]
    by_cases hy : ρ y = 0
    · simp [hy]
    · exact mul_le_mul_of_nonneg_left (hB z hz y (hys y hy)).2 (norm_nonneg _)
  have hi : Integrable (fun y => ρ y • L (x-y)) :=
    (hρ.norm.mul_const B).mono' (hm x) (Eventually.of_forall (fun y => hb y x (mem_ball_self ha)))
  refine ⟨hi, ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => ρ y * q (z-y))
    (F' := fun z y => ρ y • L (z-y))
    (bound := fun y => ‖ρ y‖ * B) ha
  · exact Eventually.of_forall (fun z => hρ.aestronglyMeasurable.mul
      (hq.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · exact NewtonExteriorResponse.source_integrand_integrable q ρ
      (fun z hz => (hd z hz).continuousAt) hρ R hc x hx
  · exact hm x
  · exact Eventually.of_forall (fun y z hz => hb y z hz)
  · exact hρ.norm.mul_const B
  · filter_upwards with y
    intro z hz
    by_cases hy : ρ y = 0
    · simp only [hy, zero_mul]
      have hz0 : (0 : ℂ) • L (z-y) = (0 : Space →L[ℝ] ℂ) :=
        _root_.zero_smul ℂ (L (z-y))
      rw [hz0]
      exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z
    · have h := (hd (z-y) (hB z hz y (hys y hy)).1).comp z ((hasFDerivAt_id z).sub_const y)
      simpa only [ContinuousLinearMap.comp_id] using h.const_mul (ρ y)

theorem hessian_measurable (k : ℝ) (i j : Fin 3) :
    Measurable (fun x => phiHessian k x i j) := by
  unfold phiHessian radialDD radialD
  fun_prop

def hessianCLM (k : ℝ) (j : Fin 3) (x : Space) : Space →L[ℝ] ℂ :=
  ∑ i : Fin 3, phiHessian k x i j • coordinateCLM i

theorem hessianCLM_basis (k : ℝ) (j : Fin 3) (x : Space) (i : Fin 3) :
    hessianCLM k j x (basis i) = phiHessian k x i j := by
  simp [hessianCLM, coordinateCLM_apply, basis, EuclideanSpace.single_apply, apply_ite]

theorem hessianCLM_measurable (k : ℝ) (j : Fin 3) : Measurable (hessianCLM k j) := by
  unfold hessianCLM
  exact Finset.measurable_sum _ (fun i _ => (hessian_measurable k i j).smul measurable_const)

theorem hessianCLM_continuousAt (k : ℝ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (hessianCLM k j) x := by
  unfold hessianCLM
  exact tendsto_finset_sum _ (fun i _ =>
    (NewtonExterior.hessian_continuousAt k i j x hx).smul continuousAt_const)

theorem gradient_hasFDerivAt (k : ℝ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    HasFDerivAt (fun y => phiGradient k y j) (hessianCLM k j x) x := by
  have hd := (KernelGradient.gradient_differentiableAt k j x hx).hasFDerivAt
  convert hd using 1
  apply ContinuousLinearMap.ext
  intro v
  have hv : (∑ i : Fin 3, v i • basis i) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, basis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  rw [← hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul, hessianCLM_basis]
  exact congrArg (fun z : ℂ => v i • z) (phiGradient_partial k x hx i j).symm

theorem gradient_response_derivative (k R : ℝ) (j : Fin 3)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    Integrable (fun y => ρ y • hessianCLM k j (x-y)) ∧
      HasFDerivAt (response (fun z => phiGradient k z j) ρ)
        (∫ y, ρ y • hessianCLM k j (x-y)) x :=
  response_derivative_off_source _ _ (KernelGradient.gradient_measurable k j)
    (hessianCLM_measurable k j) (hessianCLM_continuousAt k j)
    (gradient_hasFDerivAt k j) ρ hρ R hc x hx

theorem gradient_response_partial (k R : ℝ) (i j : Fin 3)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    dcoord (response (fun z => phiGradient k z j) ρ) x i =
      response (fun z => phiHessian k z i j) ρ x := by
  obtain ⟨hi, hd⟩ := gradient_response_derivative k R j ρ hρ hc x hx
  unfold dcoord
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [ContinuousLinearMap.smul_apply, hessianCLM_basis, smul_eq_mul, response]

theorem response_second_partial (k R : ℝ) (i j : Fin 3)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    dcoord (fun z => dcoord (response (phi k) ρ) z j) x i =
      response (fun z => phiHessian k z i j) ρ x := by
  have he : (fun z => dcoord (response (phi k) ρ) z j) =ᶠ[𝓝 x]
      (fun z => response (fun w => phiGradient k w j) ρ z) := by
    filter_upwards [((isOpen_lt continuous_const continuous_norm).mem_nhds hx :
      {z : Space | R < ‖z‖} ∈ 𝓝 x)] with z hz
    exact response_partial k R ρ hρ hc z hz j
  change (fderiv ℝ (fun z => dcoord (response (phi k) ρ) z j) x) (basis i) = _
  rw [he.fderiv_eq]
  exact gradient_response_partial k R i j ρ hρ hc x hx

theorem response_helmholtz (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    divergence (gradient (response (phi k) ρ)) x + (k : ℂ)^2 * response (phi k) ρ x = 0 := by
  have hp := NewtonExteriorResponse.source_integrand_integrable (phi k) ρ
    (fun z hz => (phi_contDiffAt k z hz).continuousAt) hρ R hc x hx
  have hh (i : Fin 3) := NewtonExteriorResponse.source_integrand_integrable
    (fun z => phiHessian k z i i) ρ (NewtonExterior.hessian_continuousAt k i i) hρ R hc x hx
  have hh01 : Integrable (fun y => ρ y * phiHessian k (x-y) 0 0 +
      ρ y * phiHessian k (x-y) 1 1) := (hh 0).add (hh 1)
  have hh012 : Integrable (fun y => (ρ y * phiHessian k (x-y) 0 0 +
      ρ y * phiHessian k (x-y) 1 1) + ρ y * phiHessian k (x-y) 2 2) := hh01.add (hh 2)
  unfold divergence pd gradient
  rw [response_second_partial k R 0 0 ρ hρ hc x hx,
    response_second_partial k R 1 1 ρ hρ hc x hx,
    response_second_partial k R 2 2 ρ hρ hc x hx]
  unfold response
  rw [← integral_const_mul, ← integral_add (hh 0) (hh 1),
    ← integral_add hh01 (hh 2),
    ← integral_add hh012 (hp.const_mul ((k : ℂ)^2))]
  apply integral_eq_zero_of_ae
  filter_upwards with y
  simp only [Pi.zero_apply]
  by_cases hy : ρ y = 0
  · simp [hy]
  · have hys : y ∈ closedBall 0 R := Classical.byContradiction (fun hn => hy (hc y hn))
    have hxy : x-y ≠ 0 := by
      intro he
      have hr : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hys
      rw [sub_eq_zero.mp he] at hx
      linarith
    have hk := phi_helmholtz k (x-y) hxy
    unfold divergence pd gradient at hk
    rw [phi_second_partial k (x-y) hxy, phi_second_partial k (x-y) hxy,
      phi_second_partial k (x-y) hxy] at hk
    linear_combination ρ y * hk

end OQ14.ScalarExteriorSecond

#print axioms OQ14.ScalarExteriorSecond.derivative_source_bound
#print axioms OQ14.ScalarExteriorSecond.response_derivative_off_source
#print axioms OQ14.ScalarExteriorSecond.hessian_measurable
#print axioms OQ14.ScalarExteriorSecond.hessianCLM_basis
#print axioms OQ14.ScalarExteriorSecond.hessianCLM_measurable
#print axioms OQ14.ScalarExteriorSecond.hessianCLM_continuousAt
#print axioms OQ14.ScalarExteriorSecond.gradient_hasFDerivAt
#print axioms OQ14.ScalarExteriorSecond.gradient_response_derivative
#print axioms OQ14.ScalarExteriorSecond.gradient_response_partial
#print axioms OQ14.ScalarExteriorSecond.response_second_partial
#print axioms OQ14.ScalarExteriorSecond.response_helmholtz

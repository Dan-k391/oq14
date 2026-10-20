import ScalarExteriorSecond

/-! # Genuine C2 exterior regularity of the scalar source potential -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ScalarExteriorRegularity

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
  OQ14.ScalarExterior OQ14.ScalarExteriorSecond Filter
open scoped Topology

theorem derivativeResponse_continuousAt (L : Space → Space →L[ℝ] ℂ)
    (hLm : Measurable L) (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContinuousAt (fun z => ∫ y, ρ y • L (z-y)) x := by
  obtain ⟨a, B, ha, hB⟩ := derivative_source_bound L hL R x hx
  have hys (y : Space) (hy : ρ y ≠ 0) : y ∈ closedBall 0 R :=
    Classical.byContradiction (fun hn => hy (hc y hn))
  apply continuousAt_of_dominated (F := fun z y => ρ y • L (z-y))
    (bound := fun y => ‖ρ y‖ * B)
  · exact Eventually.of_forall (fun z => hρ.aestronglyMeasurable.smul
      (hLm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · filter_upwards [ball_mem_nhds x ha] with z hz
    filter_upwards with y
    rw [_root_.norm_smul (ρ y) (L (z-y))]
    by_cases hy : ρ y = 0
    · simp [hy]
    · exact mul_le_mul_of_nonneg_left (hB z hz y (hys y hy)).2 (norm_nonneg _)
  · exact hρ.norm.mul_const B
  · filter_upwards with y
    by_cases hy : ρ y = 0
    · have he : (fun z : Space => ρ y • L (z-y)) = (fun _ => (0 : Space →L[ℝ] ℂ)) := by
        funext z
        rw [hy, _root_.zero_smul ℂ (L (z-y))]
      rw [he]
      exact continuousAt_const
    · exact continuousAt_const.smul
        ((hL (x-y) (hB x (mem_ball_self ha) y (hys y hy)).1).comp
          (f := fun z : Space => z-y) (continuous_id.sub continuous_const).continuousAt)

theorem kernel_response_contDiffAt_one (q : Space → ℂ) (L : Space → Space →L[ℝ] ℂ)
    (hq : Measurable q) (hLm : Measurable L)
    (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (hd : ∀ z, z ≠ 0 → HasFDerivAt q (L z) z)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ 1 (response q ρ) x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
  refine ⟨fun z => ∫ y, ρ y • L (z-y), ?_, ?_⟩
  · refine ⟨{z : Space | R < ‖z‖},
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx, ?_⟩
    intro z hz
    exact (response_derivative_off_source q L hq hLm hL hd ρ hρ R hc z hz).2
  · apply contDiffAt_zero.mpr
    refine ⟨{z : Space | R < ‖z‖},
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx, ?_⟩
    intro z hz
    exact (derivativeResponse_continuousAt L hLm hL ρ hρ R hc z hz).continuousWithinAt

theorem gradient_response_contDiffAt_one (k R : ℝ) (j : Fin 3)
    (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ 1 (response (fun z => phiGradient k z j) ρ) x :=
  kernel_response_contDiffAt_one _ _ (KernelGradient.gradient_measurable k j)
    (hessianCLM_measurable k j) (hessianCLM_continuousAt k j)
    (gradient_hasFDerivAt k j) ρ hρ R hc x hx

theorem responseDerivative_eq_sum (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    responseDerivative k ρ x =
      ∑ j : Fin 3, response (fun z => phiGradient k z j) ρ x • coordinateCLM j := by
  have hi (j : Fin 3) := NewtonExteriorResponse.source_integrand_integrable
    (fun z => phiGradient k z j) ρ
    (fun z hz => (KernelGradient.gradient_differentiableAt k j z hz).continuousAt)
    hρ R hc x hx
  unfold responseDerivative gradientCLM
  simp_rw [Finset.smul_sum, smul_smul]
  rw [integral_finset_sum _ (fun j _ => (hi j).smul_const (coordinateCLM j))]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_smul_const _ _

/-- Actual second-order continuous differentiability outside the compact
source follows from the constructed first and second derivatives. -/
theorem response_contDiffAt_two (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ 2 (response (phi k) ρ) x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨responseDerivative k ρ, ?_, ?_⟩
  · refine ⟨{z : Space | R < ‖z‖},
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx, ?_⟩
    intro z hz
    exact response_hasFDerivAt k R ρ hρ hc z hz
  · have he : responseDerivative k ρ =ᶠ[𝓝 x]
        (fun z => ∑ j : Fin 3, response (fun w => phiGradient k w j) ρ z • coordinateCLM j) := by
      filter_upwards [((isOpen_lt continuous_const continuous_norm).mem_nhds hx :
        {z : Space | R < ‖z‖} ∈ 𝓝 x)] with z hz
      exact responseDerivative_eq_sum k R ρ hρ hc z hz
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply ContDiffAt.sum
    intro j _
    let A : ℂ →L[ℝ] (Space →L[ℝ] ℂ) :=
      (ContinuousLinearMap.toSpanSingleton ℂ (coordinateCLM j)).restrictScalars ℝ
    exact A.contDiff.contDiffAt.comp x (gradient_response_contDiffAt_one k R j ρ hρ hc x hx)

theorem response_contDiffOn_two (k R : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) :
    ContDiffOn ℝ 2 (response (phi k) ρ) {x : Space | R < ‖x‖} :=
  fun x hx => (response_contDiffAt_two k R ρ hρ hc x hx).contDiffWithinAt

end OQ14.ScalarExteriorRegularity

#print axioms OQ14.ScalarExteriorRegularity.derivativeResponse_continuousAt
#print axioms OQ14.ScalarExteriorRegularity.kernel_response_contDiffAt_one
#print axioms OQ14.ScalarExteriorRegularity.gradient_response_contDiffAt_one
#print axioms OQ14.ScalarExteriorRegularity.responseDerivative_eq_sum
#print axioms OQ14.ScalarExteriorRegularity.response_contDiffAt_two
#print axioms OQ14.ScalarExteriorRegularity.response_contDiffOn_two

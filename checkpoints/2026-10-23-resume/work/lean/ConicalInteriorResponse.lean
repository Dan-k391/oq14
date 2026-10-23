import ConicalInteriorNewton

/-! Actual source-free interior dyadic integral representative and its AE identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalInteriorResponse
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.GreenKernel OQ14.NewtonExteriorResponse
  OQ14.ConicalInteriorNewton OQ14.KernelConvolution
open scoped Topology

theorem source_excluded (ρ : Space → ℂ) (a : ℝ)
    (hi : ∀ y ∈ ball (0 : Space) a, ρ y=0) (x : Space) (hx : x ∈ ball (0 : Space) a) : x ∉ tsupport ρ := by
  apply not_mem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact hi y hy

theorem source_integrand_integrable (q ρ : Space → ℂ)
    (hq : ∀ z, z≠0 → ContinuousAt q z) (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (x : Space) (hx : x ∉ tsupport ρ) : Integrable (fun y => ρ y*q (x-y)) := by
  have hqK : ContinuousOn (fun y => q (x-y)) (tsupport ρ) := by
    intro y hy
    have hn : x-y≠0 := fun h => hx ((sub_eq_zero.mp h) ▸ hy)
    exact ((hq (x-y) hn).comp (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hi := hρ.integrableOn.mul_continuousOn hqK hc
  have he : (tsupport ρ).indicator (fun y => ρ y*q (x-y))=(fun y => ρ y*q (x-y)) := by
    ext y
    by_cases hy : y ∈ tsupport ρ
    · rw [indicator_of_mem hy]
    · rw [indicator_of_not_mem hy,image_eq_zero_of_nmem_tsupport hy,zero_mul]
  rw [← he]
  exact (integrable_indicator_iff hc.measurableSet).mpr hi

theorem electric_ae_inner_ball (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a b S : ℝ) (hba : b < a)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      FieldResponse.electric k F ρ x i=ExteriorContinuity.electric k ρ x i := by
  filter_upwards [newton_ae_interior F ρ hρ hF a b S hba hc hi i] with x hx hm
  simp only [FieldResponse.electric,hx hm,← Finset.sum_add_distrib,ExteriorContinuity.electric]
  apply Finset.sum_congr rfl
  intro j _
  have hxa : x ∈ ball (0 : Space) a := ball_subset_ball hba.le hm
  have hn := source_excluded (ρ j) a (hi j) x hxa
  have hcompact := source_compact (ρ j) S (hc j)
  rw [response,← integral_add
    (source_integrand_integrable _ (ρ j) (NewtonExterior.hessian_continuousAt 0 i j) (hρ j) hcompact x hn)
    (source_integrand_integrable _ (ρ j) (remainder_continuousAt k i j) (hρ j) hcompact x hn)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [DyadicKernel.remainder]
  ring

theorem electric_ae_interior (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (a S : ℝ) (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y=0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) a → FieldResponse.electric k F ρ x=ExteriorContinuity.electric k ρ x := by
  have hh (r : ℚ) : ∀ᵐ x : Space, (r : ℝ) < a → ‖x‖ < (r : ℝ) →
      ∀ i, FieldResponse.electric k F ρ x i=ExteriorContinuity.electric k ρ x i := by
    by_cases hr : (r : ℝ) < a
    · filter_upwards [ae_all_iff.mpr (fun i => electric_ae_inner_ball k F ρ hρ hF a r S hr hc hi i)] with x hx _ hm i
      exact hx i (by simpa only [mem_ball,dist_zero_right] using hm)
    · exact Eventually.of_forall (fun _ h => False.elim (hr h))
  filter_upwards [ae_all_iff.mpr hh] with x hx hxa
  have hn : ‖x‖ < a := by simpa only [mem_ball,dist_zero_right] using hxa
  obtain ⟨r,hrx,hra⟩ := exists_rat_btwn hn
  exact funext (hx r hra hrx)

theorem electric_smooth_interior (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j)) (a : ℝ)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y=0) (i : Fin 3) (x : Space)
    (hx : x ∈ ball (0 : Space) a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ExteriorContinuity.electric k ρ y i) x := by
  apply ContDiffAt.sum
  intro j _
  exact CompactResponseSmooth.response_contDiffAt _ _ (ExteriorSmooth.dyadic_contDiffAt k i j)
    (hρ j) (hc j) x (source_excluded (ρ j) a (hi j) x hx)

end OQ14.ConicalInteriorResponse

#print axioms OQ14.ConicalInteriorResponse.source_excluded
#print axioms OQ14.ConicalInteriorResponse.source_integrand_integrable
#print axioms OQ14.ConicalInteriorResponse.electric_ae_inner_ball
#print axioms OQ14.ConicalInteriorResponse.electric_ae_interior
#print axioms OQ14.ConicalInteriorResponse.electric_smooth_interior

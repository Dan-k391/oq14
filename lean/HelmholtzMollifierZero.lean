import HelmholtzMollifiers

/-! # Actual inheritance of local zero by shrinking mollifiers

An AE-zero ball makes every genuine compact-kernel convolution exactly zero
where its reflected support remains inside that ball. The actual shrinking
normalized bumps therefore vanish eventually on every fixed strict inner ball.
No PDE or uniqueness statement is a premise of these support arguments.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.HelmholtzMollifierZero

open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.WeakPoynting
  OQ14.WeakHelmholtzRegularity OQ14.HelmholtzMollifiers
  OQ14.LocalHelmholtzRepresentation
open scoped Topology Convolution

theorem smooth_zero_of_ae_zero_ball (u ρ : Space → ℂ) (c x : Space) (r ε : ℝ)
    (hu : u =ᵐ[volume.restrict (ball c r)] 0)
    (hρ : tsupport ρ ⊆ closedBall 0 ε) (hx : ‖x-c‖+ε < r) :
    smooth ρ u x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_imp_of_ae_restrict hu] with y hy
  by_cases hρy : ρ (x-y) = 0
  · simp only [ContinuousLinearMap.mul_apply', hρy, mul_zero, Pi.zero_apply]
  · have hs : y ∈ tsupport (reflect x ρ) := subset_closure hρy
    have hb := reflect_tsupport_in_ball ρ ε r c x hρ hx hs
    simp only [ContinuousLinearMap.mul_apply', hy hb, Pi.zero_apply, zero_mul]

theorem bump_zero_on_ball (u : Space → ℂ) (c : Space) (r : ℝ)
    (hu : u =ᵐ[volume.restrict (ball c r)] 0) (φ : ContDiffBump (0 : Space)) :
    ∀ x ∈ ball c (r-φ.rOut), smooth (complexKernel φ) u x = 0 := by
  intro x hx
  have hd : ‖x-c‖+φ.rOut < r := by
    have ht : ‖x-c‖ < r-φ.rOut := by simpa only [mem_ball, dist_eq_norm] using hx
    linarith
  apply smooth_zero_of_ae_zero_ball u (complexKernel φ) c x r φ.rOut hu _ hd
  rw [complexKernel_tsupport]

theorem eventually_zero_on_fixed_ball (u : Space → ℂ) (c : Space) (r s : ℝ)
    (hs : s < r) (hu : u =ᵐ[volume.restrict (ball c r)] 0) :
    ∀ᶠ n in atTop, ∀ x ∈ ball c s, smooth (complexKernel (shrinkingBump n)) u x = 0 := by
  have he : ∀ᶠ n in atTop, (shrinkingBump n).rOut < r-s :=
    shrinkingBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hs))
  filter_upwards [he] with n hn
  intro x hx
  apply bump_zero_on_ball u c r hu (shrinkingBump n) x
  have hd : dist x c < s := hx
  exact lt_trans hd (by linarith)

theorem eventually_zero_ball_of_ae_zero_near (u : Space → ℂ) (c : Space)
    (hu : ∃ U : Set Space, U ∈ 𝓝 c ∧ u =ᵐ[volume.restrict U] 0) :
    ∃ s : ℝ, 0 < s ∧ ∀ᶠ n in atTop,
      ∀ x ∈ ball c s, smooth (complexKernel (shrinkingBump n)) u x = 0 := by
  obtain ⟨U,hU,huU⟩ := hu
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hur : u =ᵐ[volume.restrict (ball c r)] 0 := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [ae_imp_of_ae_restrict huU] with y hy
    exact fun hb => hy (hrU hb)
  exact ⟨r/2,half_pos hr,eventually_zero_on_fixed_ball u c r (r/2) (half_lt_self hr) hur⟩

theorem eventually_zero_germ_of_ae_zero_near (u : Space → ℂ) (c : Space)
    (hu : ∃ U : Set Space, U ∈ 𝓝 c ∧ u =ᵐ[volume.restrict U] 0) :
    ∀ᶠ n in atTop, smooth (complexKernel (shrinkingBump n)) u =ᶠ[𝓝 c] 0 := by
  obtain ⟨s,hs,he⟩ := eventually_zero_ball_of_ae_zero_near u c hu
  filter_upwards [he] with n hn
  exact eventually_of_mem (ball_mem_nhds c hs) hn

end OQ14.HelmholtzMollifierZero

#print axioms OQ14.HelmholtzMollifierZero.smooth_zero_of_ae_zero_ball
#print axioms OQ14.HelmholtzMollifierZero.bump_zero_on_ball
#print axioms OQ14.HelmholtzMollifierZero.eventually_zero_on_fixed_ball
#print axioms OQ14.HelmholtzMollifierZero.eventually_zero_ball_of_ae_zero_near
#print axioms OQ14.HelmholtzMollifierZero.eventually_zero_germ_of_ae_zero_near

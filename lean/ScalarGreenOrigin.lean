import ScalarGreenMoment

/-! Actual origin continuity of the Green spherical moments away from their source. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.ScalarGreenOrigin

open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.RadialMoment OQ14.SphericalMomentEquation OQ14.ScalarGreenMoment
open scoped Topology

abbrev Sphere := OQ14.AngularPower.Sphere

theorem moment_continuous (u : Space → ℂ) (hu : Continuous u) (P : Sphere → ℂ) (hP : Continuous P) :
    Continuous (moment u P) := by
  have hj : Continuous (fun z : ℝ × Sphere => u (z.1 • (z.2 : Space))*P z.2) :=
    (hu.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).mul
      (hP.comp continuous_snd)
  have h : Continuous (fun r : ℝ => ∫ n : Sphere in univ,u (r • (n : Space))*P n
      ∂OQ14.AngularPower.angularMeasure) := continuous_parametric_integral_of_continuous hj isCompact_univ
  simpa only [moment,Measure.restrict_univ] using h

theorem momentD_continuous (u : Space → ℂ) (hu : Continuous (fderiv ℝ u))
    (P : Sphere → ℂ) (hP : Continuous P) : Continuous (momentD u P) := by
  have hn : Continuous (fun z : ℝ × Sphere => (z.2 : Space)) := continuous_subtype_val.comp continuous_snd
  have hj : Continuous (fun z : ℝ × Sphere => (fderiv ℝ u (z.1 • (z.2 : Space)))
      (z.2 : Space)*P z.2) :=
    ((hu.comp (continuous_fst.smul hn)).clm_apply hn).mul (hP.comp continuous_snd)
  have h : Continuous (fun r : ℝ => ∫ n : Sphere in univ,(fderiv ℝ u (r • (n : Space))) (n : Space)*P n
      ∂OQ14.AngularPower.angularMeasure) := continuous_parametric_integral_of_continuous hj isCompact_univ
  simpa only [momentD,Measure.restrict_univ] using h

theorem kernel_origin_localization (k : ℝ) (y : Space) (hy : y ≠ 0) :
    ∃ g : Space → ℂ,ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∀ x ∈ closedBall (0 : Space) (‖y‖/2),g =ᶠ[𝓝 x] kernel k y := by
  have hΩ : IsOpen {x : Space | x ≠ y} := isOpen_ne
  have hs : closedBall (0 : Space) (‖y‖/2) ⊆ {x : Space | x ≠ y} := by
    intro x hx hxy
    have hn : ‖x‖ ≤ ‖y‖/2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    subst x
    nlinarith [norm_pos_iff.mpr hy]
  obtain ⟨g,hg,_,he⟩ := OQ14.ExteriorGreen.smooth_localization hΩ
    (isCompact_closedBall (0 : Space) (‖y‖/2)) hs (kernel k y)
    (fun x hx => kernel_contDiffAt k y x hx)
  exact ⟨g,hg,he⟩

theorem kernel_moment_origin_germ (k : ℝ) (y : Space) (hy : y ≠ 0) (P : Sphere → ℂ) :
    ∃ g : Space → ℂ,ContDiff ℝ (⊤ : ℕ∞) g ∧
      moment (kernel k y) P =ᶠ[𝓝 (0 : ℝ)] moment g P ∧
      momentD (kernel k y) P =ᶠ[𝓝 (0 : ℝ)] momentD g P := by
  obtain ⟨g,hg,he⟩ := kernel_origin_localization k y hy
  have hε : 0 < ‖y‖/2 := half_pos (norm_pos_iff.mpr hy)
  have hray (r : ℝ) (hr : r ∈ ball (0 : ℝ) (‖y‖/2)) (n : Sphere) :
      r • (n : Space) ∈ closedBall (0 : Space) (‖y‖/2) := by
    simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      OQ14.AngularPower.sphere_norm,mul_one] using
      (show |r| ≤ ‖y‖/2 from le_of_lt (by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hr))
  refine ⟨g,hg,?_,?_⟩
  · filter_upwards [ball_mem_nhds (0 : ℝ) hε] with r hr
    apply integral_congr_ae
    filter_upwards with n
    rw [← (he _ (hray r hr n)).eq_of_nhds]
  · filter_upwards [ball_mem_nhds (0 : ℝ) hε] with r hr
    apply integral_congr_ae
    filter_upwards with n
    rw [← (he _ (hray r hr n)).fderiv_eq]

theorem coefficient_continuousAt_zero (k : ℝ) (y : Space) (hy : y ≠ 0) (p : Poly) :
    ContinuousAt (coefficient k y p) 0 := by
  obtain ⟨g,hg,hU,_⟩ := kernel_moment_origin_germ k y hy (angularPolynomial p)
  exact (moment_continuous g hg.continuous _ (angularPolynomial_continuous p)).continuousAt.congr_of_eventuallyEq hU

theorem coefficientD_continuousAt_zero (k : ℝ) (y : Space) (hy : y ≠ 0) (p : Poly) :
    ContinuousAt (momentD (kernel k y) (angularPolynomial p)) 0 := by
  obtain ⟨g,hg,_,hD⟩ := kernel_moment_origin_germ k y hy (angularPolynomial p)
  exact (momentD_continuous g (hg.continuous_fderiv (by simp)) _
    (angularPolynomial_continuous p)).continuousAt.congr_of_eventuallyEq hD

end OQ14.ScalarGreenOrigin

#print axioms OQ14.ScalarGreenOrigin.moment_continuous
#print axioms OQ14.ScalarGreenOrigin.momentD_continuous
#print axioms OQ14.ScalarGreenOrigin.kernel_origin_localization
#print axioms OQ14.ScalarGreenOrigin.kernel_moment_origin_germ
#print axioms OQ14.ScalarGreenOrigin.coefficient_continuousAt_zero
#print axioms OQ14.ScalarGreenOrigin.coefficientD_continuousAt_zero

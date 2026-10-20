import RadialMoment

/-! # Actual second regularity of spherical moments -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.RadialMomentRegularity
open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.AngularPower OQ14.RadialMoment
open scoped Topology

theorem ray_joint_continuous {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (R : ℝ) (hR : 0 ≤ R)
    (hv : ContinuousOn v {x : Space | R < ‖x‖}) :
    Continuous (fun z : Ioi R × Sphere => v ((z.1 : ℝ) • (z.2 : Space))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hv.continuousAt ((exterior_open R).mem_nhds
    (ray_exterior R z.1 hR z.1.property z.2))).comp
    (f := fun z : Ioi R × Sphere => (z.1 : ℝ) • (z.2 : Space))
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).continuousAt

theorem momentDD_continuousOn (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContinuousOn (momentDD u P) (Ioi R) := by
  letI : LocallyCompactSpace (Ioi R) := isOpen_Ioi.locallyCompactSpace
  have hud := hu.fderiv_of_isOpen (exterior_open R) (m := (⊤ : ℕ∞)) (by simp)
  have hc := ray_joint_continuous (fderiv ℝ (fderiv ℝ u)) R hR
    (hud.continuousOn_fderiv_of_isOpen (exterior_open R) (by simp))
  have hn : Continuous (fun z : Ioi R × Sphere => (z.2 : Space)) :=
    continuous_subtype_val.comp continuous_snd
  have hj := ((hc.clm_apply hn).clm_apply hn).mul (hP.comp continuous_snd)
  have hi : Continuous (fun r : Ioi R => ∫ n : Sphere in univ,
      (fderiv ℝ (fderiv ℝ u) ((r : ℝ) • (n : Space))) (n : Space) (n : Space) * P n
        ∂angularMeasure) :=
    continuous_parametric_integral_of_continuous hj isCompact_univ
  rw [continuousOn_iff_continuous_restrict]
  simpa only [momentDD, Measure.restrict_univ, Set.restrict] using hi

theorem momentD_contDiffOn_one (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContDiffOn ℝ 1 (momentD u P) (Ioi R) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by simp, ?_⟩
  · intro r hr
    exact (momentD_hasDerivAt R r hR hr u hu P hP).differentiableAt.differentiableWithinAt
  · rw [contDiffOn_zero]
    exact (momentDD_continuousOn R hR u hu P hP).congr
      (fun r hr => momentD_deriv_eq R r hR hr u hu P hP)

theorem moment_contDiffOn_two (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContDiffOn ℝ 2 (moment u P) (Ioi R) := by
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨?_, by simp, ?_⟩
  · intro r hr
    exact (moment_hasDerivAt R r hR hr u hu P hP).differentiableAt.differentiableWithinAt
  · exact (momentD_contDiffOn_one R hR u hu P hP).congr
      (fun r hr => moment_deriv_eq R r hR hr u hu P hP)

end OQ14.RadialMomentRegularity

#print axioms OQ14.RadialMomentRegularity.ray_joint_continuous
#print axioms OQ14.RadialMomentRegularity.momentDD_continuousOn
#print axioms OQ14.RadialMomentRegularity.momentD_contDiffOn_one
#print axioms OQ14.RadialMomentRegularity.moment_contDiffOn_two

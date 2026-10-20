import RadialMoment

/-! # Actual spherical moment calculus on finite open annuli -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.AnnularMoment
open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.AngularPower
open scoped Topology

def annulus (R L : ℝ) : Set Space := {x | R < ‖x‖ ∧ ‖x‖ < L}

theorem annulus_open (R L : ℝ) : IsOpen (annulus R L) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem ray_annulus (R L t : ℝ) (hR : 0 ≤ R) (ht : t ∈ Ioo R L) (n : Sphere) :
    t • (n : Space) ∈ annulus R L := by
  simpa only [annulus, mem_setOf_eq, norm_smul, Real.norm_eq_abs,
    abs_of_pos (lt_of_le_of_lt hR ht.1), sphere_norm, mul_one] using ht

theorem radius_margin (R L r : ℝ) (hr : r ∈ Ioo R L) :
    ∃ ε : ℝ, 0 < ε ∧ R < r-ε ∧ r+ε < L := by
  refine ⟨min (r-R) (L-r)/2, ?_, ?_, ?_⟩
  · exact div_pos (lt_min (by linarith [hr.1]) (by linarith [hr.2])) (by norm_num)
  · linarith [min_le_left (r-R) (L-r), hr.1]
  · linarith [min_le_right (r-R) (L-r), hr.2]

theorem ball_in_interval (R L r ε : ℝ) (ha : R < r-ε) (hb : r+ε < L)
    (t : ℝ) (ht : t ∈ ball r ε) : t ∈ Ioo R L := by
  rw [mem_ball, Real.dist_eq] at ht
  exact ⟨by linarith [neg_abs_le (t-r)], by linarith [le_abs_self (t-r)]⟩

theorem annulus_comp_continuousOn {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (R L a b : ℝ) (hR : 0 ≤ R) (ha : R < a) (hb : b < L)
    (hv : ContinuousOn v (annulus R L)) :
    ContinuousOn (fun p : ℝ × Sphere => v (p.1 • (p.2 : Space))) (Icc a b ×ˢ univ) := by
  exact hv.comp (continuous_fst.smul
    (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun p hp => ray_annulus R L p.1 hR
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_le_of_lt hp.1.2 hb⟩ p.2)

theorem ray_hasDerivAt (R L t : ℝ) (hR : 0 ≤ R) (ht : t ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L)) (n : Sphere) :
    HasDerivAt (fun r : ℝ => u (r • (n : Space)))
      ((fderiv ℝ u (t • (n : Space))) (n : Space)) t := by
  have hd := (hu.contDiffAt ((annulus_open R L).mem_nhds
    (ray_annulus R L t hR ht n))).differentiableAt (by simp)
  simpa only [one_smul] using hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (n : Space))

theorem rayD_hasDerivAt (R L t : ℝ) (hR : 0 ≤ R) (ht : t ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L)) (n : Sphere) :
    HasDerivAt (fun r : ℝ => (fderiv ℝ u (r • (n : Space))) (n : Space))
      ((fderiv ℝ (fderiv ℝ u) (t • (n : Space))) (n : Space) (n : Space)) t := by
  have hud := hu.fderiv_of_isOpen (annulus_open R L) (m := (⊤ : ℕ∞)) (by simp)
  have hd := (hud.contDiffAt ((annulus_open R L).mem_nhds
    (ray_annulus R L t hR ht n))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const (n : Space))
  simpa using hc.clm_apply (hasDerivAt_const t (n : Space))

theorem moment_hasDerivAt (R L r : ℝ) (hR : 0 ≤ R) (hr : r ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    HasDerivAt (RadialMoment.moment u P) (RadialMoment.momentD u P r) r := by
  obtain ⟨ε,hε,ha,hb⟩ := radius_margin R L r hr
  have hcu := annulus_comp_continuousOn u R L (r-ε) (r+ε) hR ha hb hu.continuousOn
  have hcd := annulus_comp_continuousOn (fderiv ℝ u) R L (r-ε) (r+ε) hR ha hb
    (hu.continuousOn_fderiv_of_isOpen (annulus_open R L) (by simp))
  apply RadialMoment.integral_hasDerivAt_compact _ _ r ε hε
  · exact hcu.mul (hP.comp continuous_snd).continuousOn
  · exact (hcd.clm_apply
      (continuous_subtype_val.comp continuous_snd).continuousOn).mul
      (hP.comp continuous_snd).continuousOn
  · intro n t ht
    exact (ray_hasDerivAt R L t hR (ball_in_interval R L r ε ha hb t ht) u hu n).mul_const (P n)

theorem momentD_hasDerivAt (R L r : ℝ) (hR : 0 ≤ R) (hr : r ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    HasDerivAt (RadialMoment.momentD u P) (RadialMoment.momentDD u P r) r := by
  obtain ⟨ε,hε,ha,hb⟩ := radius_margin R L r hr
  have hud := hu.fderiv_of_isOpen (annulus_open R L) (m := (⊤ : ℕ∞)) (by simp)
  have hcd := annulus_comp_continuousOn (fderiv ℝ u) R L (r-ε) (r+ε) hR ha hb hud.continuousOn
  have hcdd := annulus_comp_continuousOn (fderiv ℝ (fderiv ℝ u)) R L (r-ε) (r+ε) hR ha hb
    (hud.continuousOn_fderiv_of_isOpen (annulus_open R L) (by simp))
  have hcn : ContinuousOn (fun p : ℝ × Sphere => (p.2 : Space))
      (Icc (r-ε) (r+ε) ×ˢ univ) := (continuous_subtype_val.comp continuous_snd).continuousOn
  apply RadialMoment.integral_hasDerivAt_compact _ _ r ε hε
  · exact (hcd.clm_apply hcn).mul (hP.comp continuous_snd).continuousOn
  · exact ((hcdd.clm_apply hcn).clm_apply hcn).mul (hP.comp continuous_snd).continuousOn
  · intro n t ht
    exact (rayD_hasDerivAt R L t hR (ball_in_interval R L r ε ha hb t ht) u hu n).mul_const (P n)

theorem ray_joint_continuous {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (R L : ℝ) (hR : 0 ≤ R) (hv : ContinuousOn v (annulus R L)) :
    Continuous (fun z : Ioo R L × Sphere => v ((z.1 : ℝ) • (z.2 : Space))) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hv.continuousAt ((annulus_open R L).mem_nhds
    (ray_annulus R L z.1 hR z.1.property z.2))).comp
    (f := fun z : Ioo R L × Sphere => (z.1 : ℝ) • (z.2 : Space))
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd)).continuousAt

theorem momentDD_continuousOn (R L : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContinuousOn (RadialMoment.momentDD u P) (Ioo R L) := by
  letI : LocallyCompactSpace (Ioo R L) := isOpen_Ioo.locallyCompactSpace
  have hud := hu.fderiv_of_isOpen (annulus_open R L) (m := (⊤ : ℕ∞)) (by simp)
  have hc := ray_joint_continuous (fderiv ℝ (fderiv ℝ u)) R L hR
    (hud.continuousOn_fderiv_of_isOpen (annulus_open R L) (by simp))
  have hn : Continuous (fun z : Ioo R L × Sphere => (z.2 : Space)) :=
    continuous_subtype_val.comp continuous_snd
  have hj := ((hc.clm_apply hn).clm_apply hn).mul (hP.comp continuous_snd)
  have hi : Continuous (fun r : Ioo R L => ∫ n : Sphere in univ,
      (fderiv ℝ (fderiv ℝ u) ((r : ℝ) • (n : Space))) (n : Space) (n : Space) * P n
        ∂angularMeasure) := continuous_parametric_integral_of_continuous hj isCompact_univ
  rw [continuousOn_iff_continuous_restrict]
  simpa only [RadialMoment.momentDD, Measure.restrict_univ, Set.restrict] using hi


theorem moment_deriv_eq (R L r : ℝ) (hR : 0 ≤ R) (hr : r ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    deriv (RadialMoment.moment u P) r = RadialMoment.momentD u P r :=
  (moment_hasDerivAt R L r hR hr u hu P hP).deriv

theorem momentD_deriv_eq (R L r : ℝ) (hR : 0 ≤ R) (hr : r ∈ Ioo R L)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    deriv (RadialMoment.momentD u P) r = RadialMoment.momentDD u P r :=
  (momentD_hasDerivAt R L r hR hr u hu P hP).deriv

theorem momentD_contDiffOn_one (R L : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContDiffOn ℝ 1 (RadialMoment.momentD u P) (Ioo R L) := by
  rw [show (1 : WithTop ℕ∞) = 0+1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, by simp, ?_⟩
  · intro r hr
    exact (momentD_hasDerivAt R L r hR hr u hu P hP).differentiableAt.differentiableWithinAt
  · rw [contDiffOn_zero]
    exact (momentDD_continuousOn R L hR u hu P hP).congr
      (fun r hr => momentD_deriv_eq R L r hR hr u hu P hP)

theorem moment_contDiffOn_two (R L : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (annulus R L))
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContDiffOn ℝ 2 (RadialMoment.moment u P) (Ioo R L) := by
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, by simp, ?_⟩
  · intro r hr
    exact (moment_hasDerivAt R L r hR hr u hu P hP).differentiableAt.differentiableWithinAt
  · exact (momentD_contDiffOn_one R L hR u hu P hP).congr
      (fun r hr => moment_deriv_eq R L r hR hr u hu P hP)
end OQ14.AnnularMoment

#print axioms OQ14.AnnularMoment.annulus_open
#print axioms OQ14.AnnularMoment.ray_annulus
#print axioms OQ14.AnnularMoment.radius_margin
#print axioms OQ14.AnnularMoment.ball_in_interval
#print axioms OQ14.AnnularMoment.annulus_comp_continuousOn
#print axioms OQ14.AnnularMoment.ray_hasDerivAt
#print axioms OQ14.AnnularMoment.rayD_hasDerivAt
#print axioms OQ14.AnnularMoment.moment_hasDerivAt
#print axioms OQ14.AnnularMoment.momentD_hasDerivAt
#print axioms OQ14.AnnularMoment.ray_joint_continuous
#print axioms OQ14.AnnularMoment.momentDD_continuousOn
#print axioms OQ14.AnnularMoment.moment_deriv_eq
#print axioms OQ14.AnnularMoment.momentD_deriv_eq
#print axioms OQ14.AnnularMoment.momentD_contDiffOn_one
#print axioms OQ14.AnnularMoment.moment_contDiffOn_two


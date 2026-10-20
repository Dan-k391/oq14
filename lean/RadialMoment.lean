import AngularPower
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Differentiation and decay of actual spherical moments -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialMoment

open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.AngularPower
open scoped Topology

def moment (u : Space → ℂ) (P : Sphere → ℂ) (r : ℝ) : ℂ :=
  ∫ n : Sphere, u (r • (n : Space)) * P n ∂angularMeasure

def momentD (u : Space → ℂ) (P : Sphere → ℂ) (r : ℝ) : ℂ :=
  ∫ n : Sphere, (fderiv ℝ u (r • (n : Space))) (n : Space) * P n ∂angularMeasure

theorem continuous_integrable {f : Sphere → ℂ} (hf : Continuous f) :
    Integrable f angularMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exterior_open (R : ℝ) : IsOpen {x : Space | R < ‖x‖} :=
  isOpen_lt continuous_const continuous_norm

theorem ray_exterior (R t : ℝ) (hR : 0 ≤ R) (ht : R < t) (n : Sphere) :
    R < ‖t • (n : Space)‖ := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hR ht),
    sphere_norm, mul_one] using ht

theorem ray_continuous (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContinuousOn u {x : Space | R < ‖x‖}) :
    Continuous (fun n : Sphere => u (r • (n : Space))) := by
  apply continuous_iff_continuousAt.mpr
  intro n
  exact (hu.continuousAt ((exterior_open R).mem_nhds (ray_exterior R r hR hr n))).comp
    (f := fun n : Sphere => r • (n : Space))
    (continuous_const.smul continuous_subtype_val).continuousAt

theorem ray_hasDerivAt (R t : ℝ) (hR : 0 ≤ R) (ht : R < t)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖}) (n : Sphere) :
    HasDerivAt (fun r : ℝ => u (r • (n : Space)))
      ((fderiv ℝ u (t • (n : Space))) (n : Space)) t := by
  have hd := (hu.contDiffAt ((exterior_open R).mem_nhds
    (ray_exterior R t hR ht n))).differentiableAt (by simp)
  simpa only [one_smul] using hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (n : Space))

theorem integral_hasDerivAt_compact
    (F F' : ℝ → Sphere → ℂ) (r ε : ℝ) (hε : 0 < ε)
    (hF : ContinuousOn (fun p : ℝ × Sphere => F p.1 p.2)
      (Icc (r-ε) (r+ε) ×ˢ univ))
    (hF' : ContinuousOn (fun p : ℝ × Sphere => F' p.1 p.2)
      (Icc (r-ε) (r+ε) ×ˢ univ))
    (hd : ∀ n t, t ∈ ball r ε → HasDerivAt (fun s => F s n) (F' t n) t) :
    HasDerivAt (fun t => ∫ n, F t n ∂angularMeasure)
      (∫ n, F' r n ∂angularMeasure) r := by
  have hs (t : ℝ) (ht : t ∈ Icc (r-ε) (r+ε)) : Continuous (F t) := by
    exact continuous_iff_continuousOn_univ.mpr (hF.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun n _ => ⟨ht, mem_univ n⟩))
  have hs' : Continuous (F' r) := by
    exact continuous_iff_continuousOn_univ.mpr (hF'.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun n _ => ⟨⟨by linarith, by linarith⟩, mem_univ n⟩))
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hF'
  have hi (t : ℝ) (ht : t ∈ ball r ε) : t ∈ Icc (r-ε) (r+ε) := by
    rw [mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [neg_abs_le (t-r)], by linarith [le_abs_self (t-r)]⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε
    (eventually_of_mem (ball_mem_nhds r hε) (fun t ht =>
      (hs t (hi t ht)).aestronglyMeasurable))
    (continuous_integrable (hs r ⟨by linarith, by linarith⟩))
    hs'.aestronglyMeasurable
    (Eventually.of_forall (fun n t ht => hC (t,n) ⟨hi t ht, mem_univ n⟩))
    (integrable_const C) (Eventually.of_forall hd)).2

theorem annulus_comp_continuousOn {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (R a b : ℝ) (hR : 0 ≤ R) (ha : R < a)
    (hv : ContinuousOn v {x : Space | R < ‖x‖}) :
    ContinuousOn (fun p : ℝ × Sphere => v (p.1 • (p.2 : Space))) (Icc a b ×ˢ univ) := by
  exact hv.comp (continuous_fst.smul
    (continuous_subtype_val.comp continuous_snd)).continuousOn
    (fun p hp => ray_exterior R p.1 hR (lt_of_lt_of_le ha hp.1.1) p.2)

theorem moment_hasDerivAt (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    HasDerivAt (moment u P) (momentD u P r) r := by
  let ε := (r-R)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha : R < r-ε := by dsimp [ε]; linarith
  have hcu := annulus_comp_continuousOn u R (r-ε) (r+ε) hR ha hu.continuousOn
  have hcd := annulus_comp_continuousOn (fderiv ℝ u) R (r-ε) (r+ε) hR ha
    (hu.continuousOn_fderiv_of_isOpen (exterior_open R) (by simp))
  apply integral_hasDerivAt_compact _ _ r ε hε
  · exact hcu.mul (hP.comp continuous_snd).continuousOn
  · exact (hcd.clm_apply
      (continuous_subtype_val.comp continuous_snd).continuousOn).mul
      (hP.comp continuous_snd).continuousOn
  · intro n t ht
    have htr : R < t := by
      rw [mem_ball, Real.dist_eq] at ht
      have := neg_abs_le (t-r)
      dsimp [ε] at ht
      linarith
    exact (ray_hasDerivAt R t hR htr u hu n).mul_const (P n)

def momentDD (u : Space → ℂ) (P : Sphere → ℂ) (r : ℝ) : ℂ :=
  ∫ n : Sphere, (fderiv ℝ (fderiv ℝ u) (r • (n : Space))) (n : Space) (n : Space) *
    P n ∂angularMeasure

theorem rayD_hasDerivAt (R t : ℝ) (hR : 0 ≤ R) (ht : R < t)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖}) (n : Sphere) :
    HasDerivAt (fun r : ℝ => (fderiv ℝ u (r • (n : Space))) (n : Space))
      ((fderiv ℝ (fderiv ℝ u) (t • (n : Space))) (n : Space) (n : Space)) t := by
  have hud := hu.fderiv_of_isOpen (exterior_open R) (m := (⊤ : ℕ∞)) (by simp)
  have hd := (hud.contDiffAt ((exterior_open R).mem_nhds
    (ray_exterior R t hR ht n))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).smul_const (n : Space))
  simpa using
    hc.clm_apply (hasDerivAt_const t (n : Space))

theorem momentD_hasDerivAt (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    HasDerivAt (momentD u P) (momentDD u P r) r := by
  let ε := (r-R)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha : R < r-ε := by dsimp [ε]; linarith
  have hud := hu.fderiv_of_isOpen (exterior_open R) (m := (⊤ : ℕ∞)) (by simp)
  have hcd := annulus_comp_continuousOn (fderiv ℝ u) R (r-ε) (r+ε) hR ha
    hud.continuousOn
  have hcdd := annulus_comp_continuousOn (fderiv ℝ (fderiv ℝ u)) R (r-ε) (r+ε) hR ha
    (hud.continuousOn_fderiv_of_isOpen (exterior_open R) (by simp))
  have hcn : ContinuousOn (fun p : ℝ × Sphere => (p.2 : Space))
      (Icc (r-ε) (r+ε) ×ˢ univ) :=
    (continuous_subtype_val.comp continuous_snd).continuousOn
  apply integral_hasDerivAt_compact _ _ r ε hε
  · exact (hcd.clm_apply hcn).mul (hP.comp continuous_snd).continuousOn
  · exact ((hcdd.clm_apply hcn).clm_apply hcn).mul (hP.comp continuous_snd).continuousOn
  · intro n t ht
    have htr : R < t := by
      rw [mem_ball, Real.dist_eq] at ht
      have := neg_abs_le (t-r)
      dsimp [ε] at ht
      linarith
    exact (rayD_hasDerivAt R t hR htr u hu n).mul_const (P n)

theorem moment_deriv_eq (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    deriv (moment u P) r = momentD u P r :=
  (moment_hasDerivAt R r hR hr u hu P hP).deriv

theorem momentD_deriv_eq (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    deriv (momentD u P) r = momentDD u P r :=
  (momentD_hasDerivAt R r hR hr u hu P hP).deriv

theorem moment_contDiffOn_one (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    ContDiffOn ℝ 1 (moment u P) (Ioi R) := by
  have hd : DifferentiableOn ℝ (moment u P) (Ioi R) :=
    fun r hr => (moment_hasDerivAt R r hR hr u hu P hP).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn (momentD u P) (Ioi R) :=
    fun r hr => (momentD_hasDerivAt R r hR hr u hu P hP).continuousAt.continuousWithinAt
  rw [show (1 : WithTop ℕ∞) = 0+1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨hd, ?_, ?_⟩
  · simp
  · rw [contDiffOn_zero]
    exact hc.congr (fun r hr => moment_deriv_eq R r hR hr u hu P hP)

theorem continuous_memLp {f : Sphere → ℂ} (hf : Continuous f) (p : ENNReal) :
    MemLp f p angularMeasure := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall (fun n => hC n (mem_univ n)))

theorem integral_pair_norm_le (f g : Sphere → ℂ) (hf : Continuous f) (hg : Continuous g) :
    ‖∫ n, f n*g n ∂angularMeasure‖ ≤
      Real.sqrt (∫ n, ‖f n‖^2 ∂angularMeasure) *
      Real.sqrt (∫ n, ‖g n‖^2 ∂angularMeasure) := by
  calc
    ‖∫ n, f n*g n ∂angularMeasure‖ ≤ ∫ n, ‖f n*g n‖ ∂angularMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ n, ‖f n‖*‖g n‖ ∂angularMeasure := by simp only [norm_mul]
    _ ≤ _ := by
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
          (continuous_memLp hf _) (continuous_memLp hg _)

def sphericalMass (u : Space → ℂ) (r : ℝ) : ℝ :=
  ∫ n : Sphere, r^2 * ‖u (r • (n : Space))‖^2 ∂angularMeasure

theorem radius_moment_norm_le (R r : ℝ) (hR : 0 ≤ R) (hr : R < r)
    (u : Space → ℂ) (hu : ContinuousOn u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) :
    ‖(r : ℂ)*moment u P r‖ ≤ Real.sqrt (sphericalMass u r) *
      Real.sqrt (∫ n, ‖P n‖^2 ∂angularMeasure) := by
  have hc := ray_continuous R r hR hr u hu
  have heq : ∀ n : Sphere, ‖(r : ℂ)*u (r • (n : Space))‖^2 =
      r^2*‖u (r • (n : Space))‖^2 := by
    intro n
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp := integral_pair_norm_le
    (fun n : Sphere => (r : ℂ)*u (r • (n : Space))) P
    (continuous_const.mul hc) hP
  simpa only [mul_assoc, integral_const_mul, moment, heq, sphericalMass] using hp

theorem radius_moment_tendsto_zero (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContinuousOn u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P)
    (hmass : Tendsto (sphericalMass u) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (r : ℂ)*moment u P r) atTop (𝓝 0) := by
  have hbound := (Real.continuous_sqrt.continuousAt.tendsto.comp hmass).mul_const
    (Real.sqrt (∫ n, ‖P n‖^2 ∂angularMeasure))
  simp only [Real.sqrt_zero, zero_mul] at hbound
  apply squeeze_zero_norm' _ hbound
  filter_upwards [eventually_gt_atTop R] with r hr
  exact radius_moment_norm_le R r hR hr u hu P hP

end OQ14.RadialMoment

#print axioms OQ14.RadialMoment.continuous_integrable
#print axioms OQ14.RadialMoment.exterior_open
#print axioms OQ14.RadialMoment.ray_exterior
#print axioms OQ14.RadialMoment.ray_continuous
#print axioms OQ14.RadialMoment.ray_hasDerivAt
#print axioms OQ14.RadialMoment.integral_hasDerivAt_compact
#print axioms OQ14.RadialMoment.annulus_comp_continuousOn
#print axioms OQ14.RadialMoment.moment_hasDerivAt
#print axioms OQ14.RadialMoment.rayD_hasDerivAt
#print axioms OQ14.RadialMoment.momentD_hasDerivAt
#print axioms OQ14.RadialMoment.moment_deriv_eq
#print axioms OQ14.RadialMoment.momentD_deriv_eq
#print axioms OQ14.RadialMoment.moment_contDiffOn_one
#print axioms OQ14.RadialMoment.continuous_memLp
#print axioms OQ14.RadialMoment.integral_pair_norm_le
#print axioms OQ14.RadialMoment.radius_moment_norm_le
#print axioms OQ14.RadialMoment.radius_moment_tendsto_zero

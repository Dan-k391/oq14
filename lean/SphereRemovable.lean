import PointSingularity
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Actual weak derivatives across spherical interfaces

Continuity removes the one-dimensional jump at the finitely many intersection
points of each coordinate line with a sphere. Fubini then gives the actual
three-dimensional integration-by-parts identity.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.SphereRemovable

open MeasureTheory OQ14.Maxwell OQ14.PointSingularity Filter Set
open scoped Topology

theorem finite_square_level (c : ℝ) : {t : ℝ | t^2 = c}.Finite := by
  by_cases he : ∃ a : ℝ, a^2 = c
  · obtain ⟨a, ha⟩ := he
    apply (Set.toFinite ({a, -a} : Set ℝ)).subset
    intro t ht
    have hh : t^2 = a^2 := ht.trans ha.symm
    simpa only [mem_insert_iff, mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp hh)
  · have hh : {t : ℝ | t^2 = c} = ∅ := by
      ext t
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun ht => he ⟨t,ht⟩
    rw [hh]
    exact finite_empty

theorem join_norm_sq (i : Fin 3) (q : Plane) (t : ℝ) :
    ‖(split i).symm (t,q)‖^2 = t^2 + q 0^2 + q 1^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin 3, ‖Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t q j‖^2) =
    t^2 + q 0^2 + q 1^2
  rw [Fin.sum_univ_three]
  fin_cases i
  · change ‖t‖^2 + ‖q 0‖^2 + ‖q 1‖^2 = _
    simp [Real.norm_eq_abs]
  · change ‖q 0‖^2 + ‖t‖^2 + ‖q 1‖^2 = _
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  · change ‖q 0‖^2 + ‖q 1‖^2 + ‖t‖^2 = _
    simp only [Real.norm_eq_abs, sq_abs]
    ring

theorem coordinate_line_sphere_finite (i : Fin 3) (q : Plane) (R : ℝ) :
    {t : ℝ | ‖(split i).symm (t,q)‖ = R}.Finite := by
  apply (finite_square_level (R^2-q 0^2-q 1^2)).subset
  intro t ht
  have h := join_norm_sq i q t
  rw [ht] at h
  dsimp only [mem_setOf_eq]
  linarith

theorem line_continuous (i : Fin 3) (q : Plane) :
    Continuous (fun t : ℝ => (split i).symm (t,q)) :=
  continuous_iff_continuousAt.mpr (fun t => (join_hasDerivAt i q t).continuousAt)

theorem line_compact_support (i : Fin 3) (q : Plane) (f : Space → ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun t : ℝ => f ((split i).symm (t,q))) := by
  obtain ⟨R,hR,hsub⟩ := hf.isBounded.subset_ball_lt 0 (0 : Space)
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro t ht
  have hm : (split i).symm (t,q) ∈ tsupport f :=
    subset_tsupport f ht
  have hb := hsub hm
  simp only [Metric.mem_ball, dist_zero_right] at hb
  have he := join_norm_sq i q t
  have hnon := norm_nonneg ((split i).symm (t,q))
  have ht2 : t^2 ≤ ‖(split i).symm (t,q)‖^2 := by
    nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
  change -R ≤ t ∧ t ≤ R
  constructor <;> nlinarith [sq_nonneg (t+R), sq_nonneg (t-R)]

/-- Compact continuous functions have zero total derivative when only a
countable exceptional set remains and the actual derivative is integrable. -/
theorem integral_derivative_off_countable
    (f f' : ℝ → ℂ) (s : Set ℝ) (hs : s.Countable)
    (hc : Continuous f) (hcompact : HasCompactSupport f)
    (hd : ∀ t, t ∉ s → HasDerivAt f (f' t) t) (hi : Integrable f') :
    (∫ t, f' t) = 0 := by
  obtain ⟨R,hR,hsub⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : ℝ)
  have ha : f (-R) = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro hm
    have h := hsub hm
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg,
      abs_of_pos hR] at h
    exact (lt_irrefl R h)
  have hb : f R = 0 := by
    apply image_eq_zero_of_nmem_tsupport
    intro hm
    have h := hsub hm
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hR] at h
    exact (lt_irrefl R h)
  have he := integral_eq_of_hasDerivWithinAt_off_countable_of_le f f'
    (show -R ≤ R by linarith) hs hc.continuousOn
    (fun t ht => hd t ht.2) hi.intervalIntegrable
  rw [ha,hb,sub_self] at he
  have hzero : ∀ᵐ t : ℝ, t ∉ Ioc (-R) R → f' t = 0 := by
    have hs' : ∀ᵐ t : ℝ, t ∉ s := by
      rw [ae_iff]
      simpa using hs.measure_zero volume
    filter_upwards [hs'] with t ht hnot
    have hn : t ∉ tsupport f := by
      intro hm
      have h := hsub hm
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at h
      exact hnot ⟨h.1,h.2.le⟩
    have hz : deriv f t = 0 := by
      rw [not_mem_tsupport_iff_eventuallyEq] at hn
      exact hn.deriv_eq.trans (deriv_const t 0)
    rw [← (hd t ht).deriv]
    exact hz
  rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
    setIntegral_eq_integral_of_ae_compl_eq_zero hzero] at he
  exact he

/-- Genuine coordinate integration by parts across a sphere, obtained from
the finite line intersections and the continuous off-countable FTC. -/
theorem integration_by_parts (i : Fin 3) (R : ℝ) (f g : Space → ℂ)
    (hfc : Continuous f) (hgc : Continuous g) (hcompact : HasCompactSupport g)
    (hf : ∀ x, ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hg : ∀ x, DifferentiableAt ℝ g x)
    (hleft : Integrable (fun x => dcoord f x i * g x))
    (hright : Integrable (fun x => f x * dcoord g x i)) :
    (∫ x, f x * dcoord g x i) = -(∫ x, dcoord f x i * g x) := by
  rw [coordinate_Fubini i _ hright, coordinate_Fubini i _ hleft, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(split_integrable i _ hleft).prod_left_ae,
    (split_integrable i _ hright).prod_left_ae] with q hl hr
  have he := integral_derivative_off_countable
    (fun t => f ((split i).symm (t,q)) * g ((split i).symm (t,q)))
    (fun t => dcoord f ((split i).symm (t,q)) i * g ((split i).symm (t,q)) +
      f ((split i).symm (t,q)) * dcoord g ((split i).symm (t,q)) i)
    {t | ‖(split i).symm (t,q)‖ = R}
    (coordinate_line_sphere_finite i q R).countable
    ((hfc.comp (line_continuous i q)).mul (hgc.comp (line_continuous i q)))
    (line_compact_support i q _ hcompact).mul_left
    (fun t ht => ((hf _ ht).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t)).mul
      ((hg _).hasFDerivAt.comp_hasDerivAt t (join_hasDerivAt i q t)))
    (hl.add hr)
  rw [integral_add hl hr] at he
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)

/-- A continuous field with actual locally integrable partial derivatives
off a sphere has the corresponding distributional partial derivative. -/
theorem weak_partial (i : Fin 3) (R : ℝ) (f f' : Space → ℂ)
    (hc : Continuous f)
    (hf : ∀ x, ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, ‖x‖ ≠ R → dcoord f x i = f' x)
    (hdloc : LocallyIntegrable f')
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (∫ x, f' x * φ x) = -(∫ x, f x * dcoord φ x i) := by
  have hs : ∀ᵐ x : Space, ‖x‖ ≠ R := by
    rw [ae_iff]
    simpa only [not_not, Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (volume : Measure Space) (0 : Space) R
  have he : (fun x => f' x * φ x) =ᵐ[volume] (fun x => dcoord f x i * φ x) := by
    filter_upwards [hs] with x hx
    rw [hder x hx]
  have hl := (test_product_integrable f' φ hdloc hφ.continuous hcompact).congr he
  have hr := test_product_integrable f (fun x => dcoord φ x i) hc.locallyIntegrable
    (partial_continuous hφ i) (hcompact.fderiv_apply ℝ (basis i))
  have hb := integration_by_parts i R f φ hc hφ.continuous hcompact hf
    (fun x => hφ.differentiable le_rfl x) hl hr
  rw [integral_congr_ae he]
  simpa only [neg_neg] using congrArg Neg.neg hb.symm

/-- The distributional curl of the actual weak gradient is zero, including
a normal jump of the gradient at the sphere. -/
theorem weak_gradient_cross_pair (R : ℝ) (f : Space → ℂ) (G : Field)
    (hc : Continuous f)
    (hf : ∀ x, ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, ‖x‖ ≠ R → ∀ i, dcoord f x i = G x i)
    (hloc : ∀ i, LocallyIntegrable (fun x => G x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (i j : Fin 3) :
    (∫ x, G x i * dcoord φ x j) = ∫ x, G x j * dcoord φ x i := by
  have hp (j : Fin 3) : ContDiff ℝ 1 (fun x => dcoord φ x j) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ φ) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
    exact hd.clm_apply contDiff_const
  rw [weak_partial i R f (fun x => G x i) hc hf (fun x hx => hder x hx i)
      (hloc i) _ (hp j) (hcompact.fderiv_apply ℝ (basis j)),
    weak_partial j R f (fun x => G x j) hc hf (fun x hx => hder x hx j)
      (hloc j) _ (hp i) (hcompact.fderiv_apply ℝ (basis i))]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [partial_comm hφ x i j]

theorem weak_gradient_curl_zero (R : ℝ) (f : Space → ℂ) (G : Field)
    (hc : Continuous f)
    (hf : ∀ x, ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, ‖x‖ ≠ R → ∀ i, dcoord f x i = G x i)
    (hloc : ∀ i, LocallyIntegrable (fun x => G x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing G φ = 0 := by
  ext j
  fin_cases j <;> dsimp [weakCurlPairing] <;>
    rw [weak_gradient_cross_pair R f G hc hf hder hloc φ hφ hcompact] <;> simp

/-- Continuous vector fields with locally integrable actual coordinate
derivatives satisfy the curl integration-by-parts identity across a sphere. -/
theorem curl_integration_by_parts (R : ℝ) (F : Field)
    (hFc : ∀ j, Continuous (fun x => F x j))
    (hFd : ∀ x, ‖x‖ ≠ R → ∀ j, DifferentiableAt ℝ (fun y => F y j) x)
    (hloc : ∀ i j, LocallyIntegrable (fun x => pd F x i j))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (fun j => ∫ x, curl F x j * φ x) = weakCurlPairing F φ := by
  have hI (i j : Fin 3) := test_product_integrable _ φ (hloc i j) hφ.continuous hcompact
  have hP (i j : Fin 3) := weak_partial i R (fun x => F x j) (fun x => pd F x i j)
    (hFc j) (fun x hx => hFd x hx j) (fun _ _ => rfl) (hloc i j) φ hφ hcompact
  ext j
  fin_cases j <;> dsimp [curl, weakCurlPairing] <;> simp only [sub_mul]
  · rw [integral_sub (hI 1 2) (hI 2 1), hP 1 2, hP 2 1]
    ring
  · rw [integral_sub (hI 2 0) (hI 0 2), hP 2 0, hP 0 2]
    ring
  · rw [integral_sub (hI 0 1) (hI 1 0), hP 0 1, hP 1 0]
    ring

end OQ14.SphereRemovable

#print axioms OQ14.SphereRemovable.finite_square_level
#print axioms OQ14.SphereRemovable.join_norm_sq
#print axioms OQ14.SphereRemovable.coordinate_line_sphere_finite
#print axioms OQ14.SphereRemovable.line_continuous
#print axioms OQ14.SphereRemovable.line_compact_support
#print axioms OQ14.SphereRemovable.integral_derivative_off_countable
#print axioms OQ14.SphereRemovable.integration_by_parts
#print axioms OQ14.SphereRemovable.weak_partial
#print axioms OQ14.SphereRemovable.weak_gradient_cross_pair
#print axioms OQ14.SphereRemovable.weak_gradient_curl_zero
#print axioms OQ14.SphereRemovable.curl_integration_by_parts

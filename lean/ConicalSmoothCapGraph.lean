import ConicalCommonSimultaneousPeaks
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Smooth inward cap graphs matching a circular cone away from a shrinking axis disk. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalSmoothCapGraph
open Metric Set Filter
open scoped Topology
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def cap (n : ℕ) (m : ℝ) (u : Plane) : ℝ :=
  Real.sqrt (m^2 * ‖u‖^2 + (ConicalTipRounding.radius n)^2 *
    ConicalTipRounding.scalarBump n (‖u‖^2))

theorem radicand_pos (n : ℕ) (m : ℝ) (hm : 0 < m) (u : Plane) :
    0 < m^2 * ‖u‖^2 + (ConicalTipRounding.radius n)^2 *
      ConicalTipRounding.scalarBump n (‖u‖^2) := by
  by_cases hu : u = 0
  · subst u
    have h : ConicalTipRounding.scalarBump n (0 : ℝ) = 1 :=
      (ConicalTipRounding.scalarBump n).one_of_mem_closedBall (by
        simp only [mem_closedBall, dist_self]; exact (ConicalTipRounding.scalarBump n).rIn_pos.le)
    simpa [h] using sq_pos_of_pos (ConicalTipRounding.radius_positive n)
  · have h1 : 0 < m^2 * ‖u‖^2 := mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos (norm_pos_iff.mpr hu))
    have h2 : 0 ≤ (ConicalTipRounding.radius n)^2 * ConicalTipRounding.scalarBump n (‖u‖^2) :=
      mul_nonneg (sq_nonneg _) ((ConicalTipRounding.scalarBump n).nonneg)
    linarith

theorem cap_smooth (n : ℕ) (m : ℝ) (hm : 0 < m) : ContDiff ℝ (⊤ : ℕ∞) (cap n m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun v : Plane => m^2 * ‖v‖^2 + (ConicalTipRounding.radius n)^2 *
      ConicalTipRounding.scalarBump n (‖v‖^2)) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add
      (contDiff_const.mul ((ConicalTipRounding.scalarBump n).contDiff.comp (contDiff_norm_sq ℝ)))
  exact (Real.contDiffAt_sqrt (radicand_pos n m hm u).ne').comp u hf.contDiffAt

theorem cap_inward (n : ℕ) (m : ℝ) (hm : 0 < m) (u : Plane) : m * ‖u‖ ≤ cap n m u := by
  have h : (m * ‖u‖)^2 ≤ m^2 * ‖u‖^2 + (ConicalTipRounding.radius n)^2 *
      ConicalTipRounding.scalarBump n (‖u‖^2) := by
    have hb : 0 ≤ (ConicalTipRounding.radius n)^2 * ConicalTipRounding.scalarBump n (‖u‖^2) :=
      mul_nonneg (sq_nonneg _) ((ConicalTipRounding.scalarBump n).nonneg)
    nlinarith
  have hs := Real.sqrt_le_sqrt h
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hm.le (norm_nonneg _)), cap] using hs

theorem cap_matches (n : ℕ) (m : ℝ) (hm : 0 < m) (u : Plane)
    (hu : 2 * ConicalTipRounding.radius n ≤ ‖u‖) : cap n m u = m * ‖u‖ := by
  have hzero : ConicalTipRounding.scalarBump n (‖u‖^2) = 0 := by
    apply (ConicalTipRounding.scalarBump n).zero_of_le_dist
    simp only [dist_zero_right, Real.norm_eq_abs, ConicalTipRounding.scalarBump]
    rw [abs_of_nonneg (sq_nonneg ‖u‖)]
    nlinarith [ConicalTipRounding.radius_positive n, norm_nonneg u]
  simp only [cap,hzero,mul_zero,add_zero, ← mul_pow, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg hm.le (norm_nonneg _))]

theorem cap_apex (n : ℕ) (m : ℝ) : cap n m 0 = ConicalTipRounding.radius n := by
  have h : ConicalTipRounding.scalarBump n (0 : ℝ) = 1 :=
    (ConicalTipRounding.scalarBump n).one_of_mem_closedBall (by
      simp only [mem_closedBall, dist_self]; exact (ConicalTipRounding.scalarBump n).rIn_pos.le)
  simp [cap,h,Real.sqrt_sq_eq_abs,abs_of_pos (ConicalTipRounding.radius_positive n)]

def sharpCone (m : ℝ) : Set (Plane × ℝ) := {x | m * ‖x.1‖ < |x.2|}

def roundedCone (n : ℕ) (m : ℝ) : Set (Plane × ℝ) :=
  {x | cap n m x.1 < |x.2|}

theorem rounded_subset (n : ℕ) (m : ℝ) (hm : 0 < m) :
    roundedCone n m ⊆ sharpCone m := by
  intro x hx
  exact lt_of_le_of_lt (cap_inward n m hm x.1) hx

theorem rounded_open (n : ℕ) (m : ℝ) (hm : 0 < m) : IsOpen (roundedCone n m) := by
  exact isOpen_lt ((cap_smooth n m hm).continuous.comp continuous_fst)
    (continuous_abs.comp continuous_snd)

theorem eventually_same (m : ℝ) (hm : 0 < m) (x : Plane × ℝ) :
    ∀ᶠ n : ℕ in atTop, (x ∈ roundedCone n m ↔ x ∈ sharpCone m) := by
  by_cases hx : x.1 = 0
  · by_cases hz : x.2 = 0
    · filter_upwards with n
      simp [roundedCone, sharpCone, hx, hz, cap_apex, (ConicalTipRounding.radius_positive n).le]
    · have ht : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
        simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
      have he := ht.eventually (gt_mem_nhds (abs_pos.mpr hz))
      filter_upwards [he] with n hn
      simp [roundedCone, sharpCone, hx, cap_apex, hn, abs_pos.mpr hz]
  · have ht : Tendsto (fun n => 2 * ConicalTipRounding.radius n) atTop (𝓝 0) := by
      simpa only [ConicalTipRounding.radius, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
    have he := ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
    filter_upwards [he] with n hn
    simp only [roundedCone, sharpCone, mem_setOf_eq, cap_matches n m hm x.1 hn.le]

end OQ14.ConicalSmoothCapGraph
#print axioms OQ14.ConicalSmoothCapGraph.radicand_pos
#print axioms OQ14.ConicalSmoothCapGraph.cap_smooth
#print axioms OQ14.ConicalSmoothCapGraph.cap_inward
#print axioms OQ14.ConicalSmoothCapGraph.cap_matches
#print axioms OQ14.ConicalSmoothCapGraph.cap_apex
#print axioms OQ14.ConicalSmoothCapGraph.rounded_subset
#print axioms OQ14.ConicalSmoothCapGraph.rounded_open
#print axioms OQ14.ConicalSmoothCapGraph.eventually_same

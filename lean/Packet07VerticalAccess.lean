import Packet07RadialMonotone

/-! Vertical access to the central corridor inside the rounded tip. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07VerticalAccess
open Set

theorem inner_vertical (n : ℕ) (m a z w : ℝ) (u : ConicalSmoothCapGraph.Plane)
    (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+2)*ConicalTipRounding.radius n < a/2)
    (hrad : (2*ConicalTipRounding.radius n)^2 < a^2/8)
    (heball : ConicalTipRounding.radius n < a^2/8)
    (hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n)
    (hz : 0 < z) (hinc : (u,z) ∈ ConicalSmoothJunction.inclusion n m a)
    (hwlo : min z (a/2) ≤ w) (hwhi : w ≤ max z (a/2)) :
    (u,w) ∈ ConicalSmoothJunction.inclusion n m a := by
  have he : 0 < ConicalTipRounding.radius n := ConicalTipRounding.radius_positive n
  have hcu := ConicalJunctionRadial.cap_upper n m hm u
  have hcapu : ConicalSmoothCapGraph.cap n m u + ConicalTipRounding.radius n < a/2 := by
    have hh := mul_le_mul_of_nonneg_left hu hm.le
    nlinarith
  have hsz : 0 < z - ConicalSmoothCapGraph.cap n m u := by
    simpa [ConicalSmoothJunction.coneMargin, abs_of_pos hz] using hinc.1
  have htz : 0 < a^2-‖u‖^2-z^2 := hinc.2.1
  have hu2 : ‖u‖^2 ≤ (2*ConicalTipRounding.radius n)^2 :=
    pow_le_pow_left₀ (norm_nonneg u) hu 2
  have hwpos : 0 < w := by
    have : 0 < min z (a/2) := lt_min hz (by linarith)
    linarith
  have hsw : 0 < w - ConicalSmoothCapGraph.cap n m u := by
    rcases le_total z (a/2) with h | h
    · rw [min_eq_left h] at hwlo
      linarith
    · rw [min_eq_right h] at hwlo
      linarith
  have htw : 0 < a^2-‖u‖^2-w^2 := by
    rcases le_total z (a/2) with h | h
    · rw [max_eq_right h] at hwhi
      have hw2 := pow_le_pow_left₀ hwpos.le hwhi 2
      nlinarith
    · rw [max_eq_left h] at hwhi
      have hw2 := pow_le_pow_left₀ hwpos.le hwhi 2
      nlinarith
  have hc0 : ConicalSmoothJunction.correction n
      (ConicalSmoothJunction.coneMargin n m (u,w))
      (ConicalSmoothJunction.ballMargin a (u,w)) = 0 := by
    apply ConicalSmoothJunction.correction_zero
    simp only [ConicalSmoothJunction.coneMargin, ConicalSmoothJunction.ballMargin,
      Prod.fst, Prod.snd, abs_of_pos hwpos]
    rcases le_total w (a/2) with h | h
    · have hw2 := pow_le_pow_left₀ hwpos.le h 2
      have htbig : ConicalTipRounding.radius n < a^2-‖u‖^2-w^2 := by nlinarith
      nlinarith [sq_nonneg (w - ConicalSmoothCapGraph.cap n m u),
        sq_nonneg (a^2-‖u‖^2-w^2-ConicalTipRounding.radius n)]
    · have hsbig : ConicalTipRounding.radius n < w - ConicalSmoothCapGraph.cap n m u := by linarith
      nlinarith [sq_nonneg (w - ConicalSmoothCapGraph.cap n m u - ConicalTipRounding.radius n),
        sq_nonneg (a^2-‖u‖^2-w^2)]
  refine ⟨?_,?_,?_⟩
  · simpa [ConicalSmoothJunction.coneMargin, abs_of_pos hwpos] using hsw
  · exact htw
  · rw [hc0]
    exact mul_pos (mul_pos (by norm_num) (by simpa [ConicalSmoothJunction.coneMargin, abs_of_pos hwpos] using hsw)) htw

/-- The stronger bounds needed for vertical access hold simultaneously for a
    finite family at all sufficiently fine rounding indices. -/
theorem eventually_vertical_bounds {ι : Type*} [Fintype ι]
    (m a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ i,
      (2*m i+2)*ConicalTipRounding.radius n < a i/2 ∧
      (2*ConicalTipRounding.radius n)^2 < (a i)^2/8 ∧
      ConicalTipRounding.radius n < (a i)^2/8 := by
  have hr : Filter.Tendsto ConicalTipRounding.radius Filter.atTop (nhds 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hr2 : Filter.Tendsto (fun n => (2*ConicalTipRounding.radius n)^2) Filter.atTop (nhds 0) := by
    simpa using (hr.const_mul 2).pow 2
  apply Filter.eventually_all.mpr
  intro i
  have hai : 0 < a i := ha i
  have hc : Filter.Tendsto (fun n => (2*m i+2)*ConicalTipRounding.radius n) Filter.atTop (nhds 0) := by
    simpa using hr.const_mul (2*m i+2)
  exact (hc.eventually (gt_mem_nhds (by positivity : 0 < a i/2))).and
    ((hr2.eventually (gt_mem_nhds (by positivity : 0 < (a i)^2/8))).and
      (hr.eventually (gt_mem_nhds (by positivity : 0 < (a i)^2/8))))
end OQ14.Packet07VerticalAccess
#print axioms OQ14.Packet07VerticalAccess.inner_vertical
#print axioms OQ14.Packet07VerticalAccess.eventually_vertical_bounds

import ConicalSmoothJunction

/-! The concrete radial derivative of the rounded cone-ball junction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalJunctionRadial
open OQ14.ConicalSmoothJunction
open Filter
open scoped Topology

theorem cap_upper (n : ℕ) (m : ℝ) (hm : 0 < m) (u : Plane) :
    ConicalSmoothCapGraph.cap n m u ≤ m*‖u‖ + ConicalTipRounding.radius n := by
  let e := ConicalTipRounding.radius n
  let b := ConicalTipRounding.scalarBump n (‖u‖^2)
  have he : 0 < e := ConicalTipRounding.radius_positive n
  have hb : b ≤ 1 := (ConicalTipRounding.scalarBump n).le_one
  have hb0 : 0 ≤ b := (ConicalTipRounding.scalarBump n).nonneg
  have hmul : e^2*b ≤ e^2 := by nlinarith [sq_nonneg e]
  have hrad : 0 ≤ m^2*‖u‖^2 + e^2*b := by positivity
  have hcross : 0 ≤ m*‖u‖*e := by positivity
  have hsquare : m^2*‖u‖^2 + e^2*b ≤ (m*‖u‖+e)^2 := by nlinarith
  have h := Real.sqrt_le_sqrt hsquare
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
  change Real.sqrt (m^2*‖u‖^2 + e^2*b) ≤ m*‖u‖+e
  exact h

theorem corner_outside_cap (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hs : coneMargin n m x < ConicalTipRounding.radius n)
    (ht : ballMargin a x < ConicalTipRounding.radius n)
    (ha : (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n < a^2) :
    2 * ConicalTipRounding.radius n ≤ ‖x.1‖ := by
  by_contra hn
  have hr : ‖x.1‖ < 2 * ConicalTipRounding.radius n := lt_of_not_ge hn
  have he := ConicalTipRounding.radius_positive n
  have hc := cap_upper n m hm x.1
  have hz : |x.2| < (2*m+2) * ConicalTipRounding.radius n := by
    have hmul := mul_lt_mul_of_pos_left hr hm
    dsimp [coneMargin] at hs
    nlinarith
  have hz0 : 0 ≤ |x.2| := abs_nonneg _
  have hr0 : 0 ≤ ‖x.1‖ := norm_nonneg _
  have hr2 := pow_lt_pow_left₀ hr hr0 (by norm_num : (2 : ℕ) ≠ 0)
  have hz2 := pow_lt_pow_left₀ hz hz0 (by norm_num : (2 : ℕ) ≠ 0)
  have heq : |x.2|^2 = x.2^2 := sq_abs _
  dsimp [ballMargin] at ht
  nlinarith

theorem eventually_separated (m a : ℝ) (ha : a ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
        ConicalTipRounding.radius n < a^2 := by
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n => (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n) atTop (𝓝 0) := by
    simpa using ((hr.pow 2).const_mul (4 + (2*m+2)^2)).add hr
  exact ht.eventually (gt_mem_nhds (sq_pos_of_ne_zero ha))

def radialDef (n : ℕ) (m a z r : ℝ) : ℝ :=
  cornerDef n (z-m*r) (a^2-r^2-z^2)

theorem radial_deriv_negative (n : ℕ) (m a z r : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hs : 0 < z-m*r)
    (ht : 0 < a^2-r^2-z^2) :
    deriv (radialDef n m a z) r < 0 := by
  let e := ConicalTipRounding.radius n
  let s := z-m*r
  let t := a^2-r^2-z^2
  let q := 1-(s^2+t^2)/e^2
  let d := deriv Real.smoothTransition q
  have he : e^2 ≠ 0 := (sq_pos_of_pos (ConicalTipRounding.radius_positive n)).ne'
  have hds : HasDerivAt (fun v : ℝ => z-m*v) (-m) r := by
    convert (hasDerivAt_const r z).sub ((hasDerivAt_const r m).mul (hasDerivAt_id r)) using 1; simp
  have hdt : HasDerivAt (fun v : ℝ => a^2-v^2-z^2) (-2*r) r := by
    convert ((hasDerivAt_const r (a^2)).sub ((hasDerivAt_id r).pow 2)).sub (hasDerivAt_const r (z^2)) using 1; simp
  have hdq := (hasDerivAt_const r (1 : ℝ)).sub
    (((hds.pow 2).add (hdt.pow 2)).div_const (e^2))
  have hdtf := ((Real.smoothTransition.contDiffAt : ContDiffAt ℝ (⊤ : ℕ∞)
    Real.smoothTransition q).differentiableAt (by norm_num)).hasDerivAt.comp r hdq
  have hder := (((hasDerivAt_const r (2 : ℝ)).mul hds).mul hdt).sub
    ((hasDerivAt_const r (e^2)).mul hdtf)
  have hfinal : HasDerivAt (radialDef n m a z)
      ((2*t+2*s*d)*(-m)+(2*s+2*t*d)*(-2*r)) r := by
    convert hder using 1
    dsimp [q,d,s,t]; field_simp; ring
  rw [hfinal.deriv]
  have hd : 0 ≤ d := transition_deriv_nonnegative q
  have hs' : 0 < s := hs
  have ht' : 0 < t := ht
  have hα : 0 < 2*t+2*s*d := by positivity
  have hβ : 0 ≤ 2*s+2*t*d := by positivity
  nlinarith [combined_radial_derivative_negative m r (2*t+2*s*d) (2*s+2*t*d) hm hr hα hβ]

end OQ14.ConicalJunctionRadial
#print axioms OQ14.ConicalJunctionRadial.radial_deriv_negative
#print axioms OQ14.ConicalJunctionRadial.cap_upper
#print axioms OQ14.ConicalJunctionRadial.corner_outside_cap
#print axioms OQ14.ConicalJunctionRadial.eventually_separated

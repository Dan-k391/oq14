import ConicalSmoothCapGraph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! An inward binary cone-ball junction with a compactly supported corner correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalSmoothJunction
open Set Metric Filter
open scoped Topology
abbrev Plane := ConicalSmoothCapGraph.Plane
abbrev Point := Plane × ℝ

theorem glue_monotone : Monotone expNegInvGlue := by
  apply monotone_of_deriv_nonneg
    ((expNegInvGlue.contDiff : ContDiff ℝ (⊤ : ℕ∞) expNegInvGlue).differentiable (by norm_num))
  intro x
  have h := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x).deriv
  simp only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  exact mul_nonneg (sq_nonneg _) (expNegInvGlue.nonneg _)

theorem glue_deriv (x : ℝ) : HasDerivAt expNegInvGlue (x⁻¹^2 * expNegInvGlue x) x := by
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 x
  simpa only [Polynomial.eval_one, one_mul, Polynomial.derivative_one, sub_zero,
    mul_one, Polynomial.eval_pow, Polynomial.eval_X] using h

theorem transition_deriv_nonnegative (x : ℝ) : 0 ≤ deriv Real.smoothTransition x := by
  let a := expNegInvGlue x
  let b := expNegInvGlue (1 - x)
  let da := x⁻¹^2 * a
  let db := (1-x)⁻¹^2 * b
  have ha : HasDerivAt expNegInvGlue da x := glue_deriv x
  have hb : HasDerivAt (fun y : ℝ => expNegInvGlue (1-y)) (-db) x := by
    convert (glue_deriv (1-x)).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1; simp [db,b]
  have hd := ha.div (ha.add hb) (Real.smoothTransition.pos_denom x).ne'
  have hh : HasDerivAt Real.smoothTransition ((da*b+a*db)/(a+b)^2) x := by
    convert hd using 1; dsimp [a,b,da,db,Real.smoothTransition]; ring
  rw [hh.deriv]
  have hapos : 0 ≤ a := expNegInvGlue.nonneg _
  have hbpos : 0 ≤ b := expNegInvGlue.nonneg _
  exact div_nonneg (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hapos) hbpos)
    (mul_nonneg hapos (mul_nonneg (sq_nonneg _) hbpos))) (sq_nonneg _)

theorem transition_monotone : Monotone Real.smoothTransition := by
  intro x y hxy
  unfold Real.smoothTransition
  rw [div_le_div_iff₀ (Real.smoothTransition.pos_denom x) (Real.smoothTransition.pos_denom y)]
  have ha := glue_monotone hxy
  have hb := glue_monotone (sub_le_sub_left hxy 1)
  have h1 := expNegInvGlue.nonneg x
  have h2 := expNegInvGlue.nonneg (1-y)
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) h2,
    mul_nonneg h1 (sub_nonneg.mpr hb)]

def coneMargin (n : ℕ) (m : ℝ) (x : Point) : ℝ :=
  |x.2| - ConicalSmoothCapGraph.cap n m x.1

def ballMargin (a : ℝ) (x : Point) : ℝ := a^2 - ‖x.1‖^2 - x.2^2

def correction (n : ℕ) (s t : ℝ) : ℝ :=
  (ConicalTipRounding.radius n)^2 *
    Real.smoothTransition (1 - (s^2+t^2)/(ConicalTipRounding.radius n)^2)

def cornerDef (n : ℕ) (s t : ℝ) : ℝ := 2*s*t - correction n s t

theorem corner_partial_positive (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < deriv (fun v => cornerDef n v t) s := by
  let e := ConicalTipRounding.radius n
  let q := 1 - (s^2+t^2)/e^2
  let d := deriv Real.smoothTransition q
  have he : e^2 ≠ 0 := (sq_pos_of_pos (ConicalTipRounding.radius_positive n)).ne'
  have hq : HasDerivAt (fun v : ℝ => 1 - (v^2+t^2)/e^2) (-(2*s/e^2)) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub
      (((hasDerivAt_id s).pow 2 |>.add (hasDerivAt_const s (t^2))).div_const (e^2)) using 1; simp only [id_eq]; ring
  have hd := ((Real.smoothTransition.contDiffAt : ContDiffAt ℝ (⊤ : ℕ∞) Real.smoothTransition q).differentiableAt (by norm_num)).hasDerivAt.comp s hq
  have hf := (((hasDerivAt_const s (2 : ℝ)).mul (hasDerivAt_id s)).mul (hasDerivAt_const s t)).sub
    ((hasDerivAt_const s (e^2)).mul hd)
  have hfinal : HasDerivAt (fun v => cornerDef n v t) (2*t+2*s*d) s := by
    convert hf using 1
    dsimp [q, d]; field_simp; ring
  rw [hfinal.deriv]
  have hd0 : 0 ≤ d := transition_deriv_nonnegative q
  positivity

theorem corner_symmetric (n : ℕ) (s t : ℝ) : cornerDef n s t = cornerDef n t s := by
  simp only [cornerDef, correction, add_comm, mul_comm, mul_left_comm]

theorem corner_partial_second_positive (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < deriv (fun v => cornerDef n s v) t := by
  have heq : (fun v => cornerDef n s v) = (fun v => cornerDef n v s) := by
    funext v
    exact corner_symmetric n s v
  rw [heq]
  exact corner_partial_positive n t s ht hs

theorem combined_radial_derivative_negative (m r α β : ℝ)
    (hm : 0 < m) (hr : 0 ≤ r) (hα : 0 < α) (hβ : 0 ≤ β) :
    -α*m - 2*β*r < 0 := by
  have h1 := mul_pos hα hm
  have h2 := mul_nonneg hβ hr
  nlinarith

def defining (n : ℕ) (m a : ℝ) (x : Point) : ℝ :=
  2 * coneMargin n m x * ballMargin a x -
    correction n (coneMargin n m x) (ballMargin a x)

def inclusion (n : ℕ) (m a : ℝ) : Set Point :=
  {x | 0 < coneMargin n m x ∧ 0 < ballMargin a x ∧
    correction n (coneMargin n m x) (ballMargin a x) <
      2 * coneMargin n m x * ballMargin a x}

theorem correction_nonnegative (n : ℕ) (s t : ℝ) : 0 ≤ correction n s t :=
  mul_nonneg (sq_nonneg _) (Real.smoothTransition.nonneg _)

theorem correction_zero (n : ℕ) (s t : ℝ)
    (h : (ConicalTipRounding.radius n)^2 ≤ s^2+t^2) : correction n s t = 0 := by
  have hp : 0 < (ConicalTipRounding.radius n)^2 := sq_pos_of_pos (ConicalTipRounding.radius_positive n)
  have hz : 1 - (s^2+t^2)/(ConicalTipRounding.radius n)^2 ≤ 0 := by
    rw [sub_nonpos, one_le_div hp]
    exact h
  simp [correction, Real.smoothTransition.zero_of_nonpos hz]

theorem inclusion_subset (n : ℕ) (m a : ℝ) (hm : 0 < m) :
    inclusion n m a ⊆ ConicalSmoothCapGraph.sharpCone m ∩ {x | 0 < ballMargin a x} := by
  intro x hx
  constructor
  · have hc := ConicalSmoothCapGraph.cap_inward n m hm x.1
    exact lt_of_le_of_lt hc (sub_pos.mp hx.1)
  · exact hx.2.1

theorem inclusion_bounded (n : ℕ) (m a : ℝ) (ha : 0 < a) (x : Point)
    (hx : x ∈ inclusion n m a) : ‖x.1‖ < a ∧ |x.2| < a := by
  have ht : 0 < a^2 - ‖x.1‖^2 - x.2^2 := hx.2.1
  have hz : 0 ≤ ‖x.1‖ := norm_nonneg _
  have habs : 0 ≤ |x.2| := abs_nonneg _
  have habs_sq : |x.2|^2 = x.2^2 := sq_abs _
  constructor <;> nlinarith [sq_nonneg (‖x.1‖ - a), sq_nonneg (|x.2| - a)]

theorem inclusion_matches (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hcap : 2 * ConicalTipRounding.radius n ≤ ‖x.1‖)
    (hj : (ConicalTipRounding.radius n)^2 ≤
      (|x.2| - m * ‖x.1‖)^2 + (ballMargin a x)^2) :
    (x ∈ inclusion n m a ↔
      x ∈ ConicalSmoothCapGraph.sharpCone m ∩ {x | 0 < ballMargin a x}) := by
  have hcm : coneMargin n m x = |x.2| - m * ‖x.1‖ := by
    simp [coneMargin, ConicalSmoothCapGraph.cap_matches n m hm x.1 hcap]
  have hz : correction n (coneMargin n m x) (ballMargin a x) = 0 := by
    apply correction_zero
    rw [hcm]
    exact hj
  simp only [inclusion, mem_setOf_eq, mem_inter_iff, ConicalSmoothCapGraph.sharpCone,
    hz, hcm, sub_pos]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hs, ht⟩
    refine ⟨hs, ht, ?_⟩
    rw [← hcm, hz]
    rw [hcm]
    nlinarith [mul_pos (sub_pos.mpr hs) ht]

theorem inclusion_open (n : ℕ) (m a : ℝ) (hm : 0 < m) : IsOpen (inclusion n m a) := by
  have hs : Continuous (coneMargin n m) :=
    (continuous_abs.comp continuous_snd).sub ((ConicalSmoothCapGraph.cap_smooth n m hm).continuous.comp continuous_fst)
  have ht : Continuous (ballMargin a) :=
    (continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub (continuous_snd.pow 2)
  have hb : Continuous (fun x : Point => correction n (coneMargin n m x) (ballMargin a x)) := by
    unfold correction
    exact continuous_const.mul (Real.smoothTransition.continuous.comp
      (continuous_const.sub (((hs.pow 2).add (ht.pow 2)).div_const _)))
  exact (isOpen_lt continuous_const hs).inter ((isOpen_lt continuous_const ht).inter
    (isOpen_lt hb ((continuous_const.mul hs).mul ht)))

theorem defining_smooth_at (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x.2 ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (defining n m a) x := by
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (coneMargin n m) x := by
    unfold coneMargin
    have habs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Point => |y.2|) x := by
      simpa only [Real.norm_eq_abs] using
        (contDiffAt_norm ℝ hx).comp x (contDiff_snd.contDiffAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Point => y.2) x)
    exact habs.sub
      ((ConicalSmoothCapGraph.cap_smooth n m hm).comp contDiff_fst).contDiffAt
  have ht : ContDiffAt ℝ (⊤ : ℕ∞) (ballMargin a) x := by
    unfold ballMargin
    exact ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)).sub
      (contDiff_snd.pow 2)).contDiffAt
  unfold defining correction
  exact ((contDiffAt_const.mul hs).mul ht).sub
    (contDiffAt_const.mul (Real.smoothTransition.contDiffAt.comp x
      (contDiffAt_const.sub (((hs.pow 2).add (ht.pow 2)).div_const _))))

theorem eventually_matches (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x.1 ≠ 0)
    (hj : 0 < (|x.2| - m * ‖x.1‖)^2 + (ballMargin a x)^2) :
    ∀ᶠ n : ℕ in atTop, (x ∈ inclusion n m a ↔
      x ∈ ConicalSmoothCapGraph.sharpCone m ∩ {x | 0 < ballMargin a x}) := by
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have htwo : Tendsto (fun n => 2 * ConicalTipRounding.radius n) atTop (𝓝 0) := by
    simpa using hr.const_mul 2
  have hcap := htwo.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
  have hsquare : Tendsto (fun n => (ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by
    simpa using hr.pow 2
  have hcorner := hsquare.eventually (gt_mem_nhds hj)
  filter_upwards [hcap, hcorner] with n hn hc
  exact inclusion_matches n m a hm x hn.le hc.le

end OQ14.ConicalSmoothJunction
#print axioms OQ14.ConicalSmoothJunction.correction_nonnegative
#print axioms OQ14.ConicalSmoothJunction.transition_deriv_nonnegative
#print axioms OQ14.ConicalSmoothJunction.corner_partial_positive
#print axioms OQ14.ConicalSmoothJunction.corner_partial_second_positive
#print axioms OQ14.ConicalSmoothJunction.combined_radial_derivative_negative
#print axioms OQ14.ConicalSmoothJunction.correction_zero
#print axioms OQ14.ConicalSmoothJunction.inclusion_subset
#print axioms OQ14.ConicalSmoothJunction.inclusion_bounded
#print axioms OQ14.ConicalSmoothJunction.inclusion_matches
#print axioms OQ14.ConicalSmoothJunction.inclusion_open
#print axioms OQ14.ConicalSmoothJunction.defining_smooth_at
#print axioms OQ14.ConicalSmoothJunction.eventually_matches

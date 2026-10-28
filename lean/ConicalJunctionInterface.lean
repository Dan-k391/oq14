import ConicalJunctionRadial

/-! Radial nondegeneracy of the explicit physical junction defining function. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalJunctionInterface
open OQ14.ConicalSmoothJunction OQ14.ConicalJunctionRadial Filter
open scoped Topology

theorem frontier_nonzero_axial (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a)) : x.2 ≠ 0 := by
  have hc : IsClosed {y : Point | ConicalSmoothCapGraph.cap n m y.1 ≤ |y.2|} :=
    isClosed_le ((ConicalSmoothCapGraph.cap_smooth n m hm).continuous.comp continuous_fst)
      (continuous_abs.comp continuous_snd)
  have hsub : inclusion n m a ⊆ {y : Point | ConicalSmoothCapGraph.cap n m y.1 ≤ |y.2|} := by
    intro y hy
    exact (sub_pos.mp hy.1).le
  have hh := (closure_minimal hsub hc) (frontier_subset_closure hx)
  intro hz
  simp only [Set.mem_setOf_eq, hz, abs_zero] at hh
  have hp : 0 < ConicalSmoothCapGraph.cap n m x.1 :=
    Real.sqrt_pos.2 (ConicalSmoothCapGraph.radicand_pos n m hm x.1)
  linarith

theorem defining_continuous (n : ℕ) (m a : ℝ) (hm : 0 < m) : Continuous (defining n m a) := by
  have hs : Continuous (coneMargin n m) :=
    (continuous_abs.comp continuous_snd).sub ((ConicalSmoothCapGraph.cap_smooth n m hm).continuous.comp continuous_fst)
  have ht : Continuous (ballMargin a) :=
    (continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub (continuous_snd.pow 2)
  unfold defining correction
  exact ((continuous_const.mul hs).mul ht).sub (continuous_const.mul
    (Real.smoothTransition.continuous.comp
      (continuous_const.sub (((hs.pow 2).add (ht.pow 2)).div_const _))))

theorem frontier_margins (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a)) :
    0 ≤ coneMargin n m x ∧ 0 ≤ ballMargin a x ∧ defining n m a x = 0 := by
  have hs : Continuous (coneMargin n m) :=
    (continuous_abs.comp continuous_snd).sub ((ConicalSmoothCapGraph.cap_smooth n m hm).continuous.comp continuous_fst)
  have ht : Continuous (ballMargin a) :=
    (continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub (continuous_snd.pow 2)
  have hf := defining_continuous n m a hm
  let C : Set Point := {y | 0 ≤ coneMargin n m y ∧ 0 ≤ ballMargin a y ∧ 0 ≤ defining n m a y}
  have hc : IsClosed C := (isClosed_le continuous_const hs).inter
    ((isClosed_le continuous_const ht).inter (isClosed_le continuous_const hf))
  have hsub : inclusion n m a ⊆ C := by
    intro y hy
    exact ⟨hy.1.le, hy.2.1.le, sub_nonneg.mpr hy.2.2.le⟩
  have hh := (closure_minimal hsub hc) (frontier_subset_closure hx)
  have hn : x ∉ inclusion n m a := by
    have hi : interior (inclusion n m a) = inclusion n m a := (inclusion_open n m a hm).interior_eq
    intro hx'
    exact (Set.disjoint_left.mp disjoint_interior_frontier) (hi.symm ▸ hx') hx
  refine ⟨hh.1, hh.2.1, ?_⟩
  apply le_antisymm _ hh.2.2
  by_contra h
  have hfpos : 0 < defining n m a x := lt_of_not_ge h
  have hc0 := correction_nonnegative n (coneMargin n m x) (ballMargin a x)
  have hp : 0 < 2 * coneMargin n m x * ballMargin a x := by
    dsimp [defining] at hfpos
    linarith
  have hsm : 0 < coneMargin n m x := by
    by_contra hsm
    have : coneMargin n m x = 0 := le_antisymm (le_of_not_gt hsm) hh.1
    simp [this] at hp
  have htm : 0 < ballMargin a x := by
    by_contra htm
    have : ballMargin a x = 0 := le_antisymm (le_of_not_gt htm) hh.2.1
    simp [this] at hp
  apply hn
  refine ⟨hsm, htm, ?_⟩
  dsimp [defining] at hfpos
  linarith

theorem frontier_one_margin_positive (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a)) :
    0 < coneMargin n m x ∨ 0 < ballMargin a x := by
  have h := frontier_margins n m a hm x hx
  by_contra hn
  push_neg at hn
  have hs : coneMargin n m x = 0 := le_antisymm hn.1 h.1
  have ht : ballMargin a x = 0 := le_antisymm hn.2 h.2.1
  have hf := h.2.2
  simp [defining, correction, hs, ht] at hf
  exact (ConicalTipRounding.radius_positive n).ne' hf

theorem corner_outside_cap_strict (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hs : coneMargin n m x < ConicalTipRounding.radius n)
    (ht : ballMargin a x < ConicalTipRounding.radius n)
    (ha : (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n < a^2) :
    2 * ConicalTipRounding.radius n < ‖x.1‖ := by
  by_contra hn
  have hr : ‖x.1‖ ≤ 2 * ConicalTipRounding.radius n := le_of_not_gt hn
  have he := ConicalTipRounding.radius_positive n
  have hc := cap_upper n m hm x.1
  have hz : |x.2| < (2*m+2) * ConicalTipRounding.radius n := by
    have hmul := mul_le_mul_of_nonneg_left hr hm.le
    dsimp [coneMargin] at hs
    nlinarith
  have hz0 : 0 ≤ |x.2| := abs_nonneg _
  have hr0 : 0 ≤ ‖x.1‖ := norm_nonneg _
  have hr2 := pow_le_pow_left₀ hr0 hr 2
  have hz2 := pow_lt_pow_left₀ hz hz0 (by norm_num : (2 : ℕ) ≠ 0)
  have heq : |x.2|^2 = x.2^2 := sq_abs _
  dsimp [ballMargin] at ht
  nlinarith

def radialPath (x : Point) (v : ℝ) : Point := (v • x.1, x.2)

theorem radial_representation (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hr : 2 * ConicalTipRounding.radius n < ‖x.1‖) :
    (fun v => defining n m a (radialPath x v)) =ᶠ[𝓝 (1 : ℝ)]
      (fun v => radialDef n m a |x.2| (v * ‖x.1‖)) := by
  have hv : ∀ᶠ v : ℝ in 𝓝 1, 0 < v := lt_mem_nhds (by norm_num)
  have hw : ∀ᶠ v : ℝ in 𝓝 1, 2 * ConicalTipRounding.radius n < v*‖x.1‖ := by
    have hc : Continuous (fun v : ℝ => v*‖x.1‖) := continuous_id.mul continuous_const
    exact hc.continuousAt.eventually (by simpa using lt_mem_nhds hr)
  filter_upwards [hv,hw] with v hv' hw'
  have hnorm : ‖v • x.1‖ = v * ‖x.1‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hv']
  have hcap := ConicalSmoothCapGraph.cap_matches n m hm (v • x.1) (by rw [hnorm]; exact hw'.le)
  dsimp [defining, coneMargin, ballMargin, radialPath, radialDef, cornerDef]
  rw [hcap, hnorm, sq_abs]

theorem radialDef_smooth (n : ℕ) (m a z : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialDef n m a z) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => z-m*r) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => a^2-r^2-z^2) :=
    (contDiff_const.sub (contDiff_id.pow 2)).sub contDiff_const
  unfold radialDef cornerDef correction
  exact ((contDiff_const.mul hs).mul ht).sub (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (((hs.pow 2).add (ht.pow 2)).div_const _))))

theorem radial_path_deriv_negative (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hr : 2 * ConicalTipRounding.radius n < ‖x.1‖)
    (hs : 0 < coneMargin n m x) (ht : 0 < ballMargin a x) :
    deriv (fun v => defining n m a (radialPath x v)) 1 < 0 := by
  have hcap := ConicalSmoothCapGraph.cap_matches n m hm x.1 hr.le
  have hs' : 0 < |x.2|-m*‖x.1‖ := by simpa [coneMargin, hcap] using hs
  have ht' : 0 < a^2-‖x.1‖^2-|x.2|^2 := by simpa [ballMargin, sq_abs] using ht
  have hn : 0 < ‖x.1‖ := lt_trans (mul_pos (by norm_num) (ConicalTipRounding.radius_positive n)) hr
  have hd := radial_deriv_negative n m a |x.2| ‖x.1‖ hm hn.le hs' ht'
  have hder : HasDerivAt (radialDef n m a |x.2|)
      (deriv (radialDef n m a |x.2|) ‖x.1‖) ‖x.1‖ :=
    ((radialDef_smooth n m a |x.2|).differentiable (by norm_num) ‖x.1‖).hasDerivAt
  have hder' : HasDerivAt (radialDef n m a |x.2|)
      (deriv (radialDef n m a |x.2|) ‖x.1‖) ((1 : ℝ)*‖x.1‖) := by simpa using hder
  have hcomp := hder'.comp 1 ((hasDerivAt_id (1 : ℝ)).mul_const ‖x.1‖)
  have hcomp' : HasDerivAt (fun v => radialDef n m a |x.2| (v * ‖x.1‖))
      (deriv (radialDef n m a |x.2|) ‖x.1‖ * ‖x.1‖) 1 := by
    simpa only [one_mul, Function.comp_def, id_eq] using hcomp
  have hpath : HasDerivAt (fun v => defining n m a (radialPath x v))
      (deriv (radialDef n m a |x.2|) ‖x.1‖ * ‖x.1‖) 1 := by
    apply hcomp'.congr_of_eventuallyEq
    exact radial_representation n m a hm x hr
  rw [hpath.deriv]
  exact mul_neg_of_neg_of_pos hd hn

theorem frontier_corner_margins_small (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a))
    (hs : 0 < coneMargin n m x) (ht : 0 < ballMargin a x) :
    coneMargin n m x < ConicalTipRounding.radius n ∧
      ballMargin a x < ConicalTipRounding.radius n := by
  let e := ConicalTipRounding.radius n
  let s := coneMargin n m x
  let t := ballMargin a x
  have he : 0 < e := ConicalTipRounding.radius_positive n
  have hf := (frontier_margins n m a hm x hx).2.2
  have hc : 0 < correction n s t := by
    change 2*s*t - correction n s t = 0 at hf
    nlinarith [mul_pos hs ht]
  have harg : 0 < 1-(s^2+t^2)/e^2 := by
    by_contra h
    have hz := Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)
    have : correction n s t = 0 := by simp [correction, e, hz]
    linarith
  have hsq : s^2+t^2 < e^2 := by
    have hq := (div_lt_one (sq_pos_of_pos he)).mp (sub_pos.mp harg)
    exact hq
  constructor <;> dsimp [s,t,e] at * <;> nlinarith [sq_nonneg (s-t)]

theorem frontier_corner_radial_negative (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a))
    (hs : 0 < coneMargin n m x) (ht : 0 < ballMargin a x)
    (ha : (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n < a^2) :
    deriv (fun v => defining n m a (radialPath x v)) 1 < 0 := by
  have hsmall := frontier_corner_margins_small n m a hm x hx hs ht
  exact radial_path_deriv_negative n m a hm x
    (corner_outside_cap_strict n m a hm x hsmall.1 hsmall.2 ha) hs ht

theorem transition_deriv_zero_of_nonpos (q : ℝ) (hq : q ≤ 0) :
    deriv Real.smoothTransition q = 0 := by
  have hzero := Real.smoothTransition.zero_of_nonpos hq
  have hmin : IsLocalMin Real.smoothTransition q := by
    exact Filter.Eventually.of_forall (fun y => by rw [hzero]; exact Real.smoothTransition.nonneg y)
  exact hmin.deriv_eq_zero

def axialPath (x : Point) (v : ℝ) : Point := (x.1, v*x.2)

def axialDef (n : ℕ) (m a : ℝ) (x : Point) (v : ℝ) : ℝ :=
  cornerDef n (v*|x.2|-ConicalSmoothCapGraph.cap n m x.1)
    (a^2-‖x.1‖^2-(v*x.2)^2)

theorem axial_representation (n : ℕ) (m a : ℝ) (x : Point) :
    (fun v => defining n m a (axialPath x v)) =ᶠ[𝓝 (1 : ℝ)] axialDef n m a x := by
  filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with v hv
  simp [defining, axialPath, axialDef, cornerDef, coneMargin, ballMargin,
    abs_mul, abs_of_pos hv]

theorem axial_deriv_formula (n : ℕ) (m a : ℝ) (x : Point) :
    deriv (fun v => defining n m a (axialPath x v)) 1 =
      (2*ballMargin a x + 2*coneMargin n m x *
        deriv Real.smoothTransition (1-(coneMargin n m x^2 + ballMargin a x^2)/(ConicalTipRounding.radius n)^2)) * |x.2| +
      (2*coneMargin n m x + 2*ballMargin a x *
        deriv Real.smoothTransition (1-(coneMargin n m x^2 + ballMargin a x^2)/(ConicalTipRounding.radius n)^2)) * (-2*x.2^2) := by
  let e := ConicalTipRounding.radius n
  let s := coneMargin n m x
  let t := ballMargin a x
  let q := 1-(s^2+t^2)/e^2
  let d := deriv Real.smoothTransition q
  have he : e^2 ≠ 0 := (sq_pos_of_pos (ConicalTipRounding.radius_positive n)).ne'
  have hds : HasDerivAt (fun v : ℝ => v*|x.2|-ConicalSmoothCapGraph.cap n m x.1) |x.2| 1 := by
    convert ((hasDerivAt_id (1 : ℝ)).mul_const |x.2|).sub
      (hasDerivAt_const 1 (ConicalSmoothCapGraph.cap n m x.1)) using 1; simp
  have hdt : HasDerivAt (fun v : ℝ => a^2-‖x.1‖^2-(v*x.2)^2) (-2*x.2^2) 1 := by
    convert (hasDerivAt_const 1 (a^2-‖x.1‖^2)).sub
      (((hasDerivAt_id (1 : ℝ)).mul_const x.2).pow 2) using 1; simp; ring
  have hdq := (hasDerivAt_const 1 (1 : ℝ)).sub (((hds.pow 2).add (hdt.pow 2)).div_const (e^2))
  have hd := ((Real.smoothTransition.contDiffAt : ContDiffAt ℝ (⊤ : ℕ∞)
    Real.smoothTransition q).differentiableAt (by norm_num)).hasDerivAt
  have hd' : HasDerivAt Real.smoothTransition d
      (1-((1*|x.2|-ConicalSmoothCapGraph.cap n m x.1)^2+
        (a^2-‖x.1‖^2-(1*x.2)^2)^2)/e^2) := by
    have hqeq : 1-((1*|x.2|-ConicalSmoothCapGraph.cap n m x.1)^2+
        (a^2-‖x.1‖^2-(1*x.2)^2)^2)/e^2 = q := by simp [q,s,t,coneMargin,ballMargin]
    rw [hqeq]
    exact hd
  have htr := hd'.comp 1 hdq
  have hder := (((hasDerivAt_const 1 (2 : ℝ)).mul hds).mul hdt).sub
    ((hasDerivAt_const 1 (e^2)).mul htr)
  have hfinal : HasDerivAt (axialDef n m a x)
      ((2*t+2*s*d)*|x.2|+(2*s+2*t*d)*(-2*x.2^2)) 1 := by
    convert hder using 1
    dsimp [q,d,s,t,coneMargin,ballMargin]; field_simp; ring
  have hpath := hfinal.congr_of_eventuallyEq (axial_representation n m a x)
  simpa only [q, d, s, t, e] using hpath.deriv

theorem frontier_edge_axial_nonzero (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a))
    (hedge : coneMargin n m x = 0 ∨ ballMargin a x = 0) :
    deriv (fun v => defining n m a (axialPath x v)) 1 ≠ 0 := by
  have hmarg := frontier_margins n m a hm x hx
  have hpos := frontier_one_margin_positive n m a hm x hx
  have hz : x.2 ≠ 0 := frontier_nonzero_axial n m a hm x hx
  have hc : correction n (coneMargin n m x) (ballMargin a x) = 0 := by
    have hf := hmarg.2.2
    rcases hedge with hs | ht
    · simpa [defining, hs] using hf
    · simpa [defining, ht] using hf
  have htrans : Real.smoothTransition (1-(coneMargin n m x^2 + ballMargin a x^2)/
      (ConicalTipRounding.radius n)^2) = 0 := by
    have hp : (ConicalTipRounding.radius n)^2 ≠ 0 := (sq_pos_of_pos (ConicalTipRounding.radius_positive n)).ne'
    exact (mul_eq_zero.mp hc).resolve_left hp
  have hd := transition_deriv_zero_of_nonpos _ (Real.smoothTransition.zero_iff_nonpos.mp htrans)
  rw [axial_deriv_formula, hd]
  rcases hedge with hs | ht
  · have htpos : 0 < ballMargin a x := by
      rcases hpos with h | h
      · linarith
      · exact h
    simp only [hs, zero_mul, mul_zero, zero_add, add_zero]
    exact ne_of_gt (mul_pos (by positivity) (abs_pos.mpr hz))
  · have hspos : 0 < coneMargin n m x := by
      rcases hpos with h | h
      · exact h
      · linarith
    simp only [ht, zero_mul, mul_zero, zero_add, add_zero]
    have hsq : 0 < x.2^2 := sq_pos_of_ne_zero hz
    exact ne_of_lt (mul_neg_of_pos_of_neg (by positivity) (by nlinarith))

theorem frontier_fderiv_nonzero (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a))
    (ha : (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n < a^2) :
    fderiv ℝ (defining n m a) x ≠ 0 := by
  have hz := frontier_nonzero_axial n m a hm x hx
  have hf := ((defining_smooth_at n m a hm x hz).differentiableAt (by norm_num)).hasFDerivAt
  have hmargin := frontier_margins n m a hm x hx
  by_cases hs : 0 < coneMargin n m x
  · by_cases ht : 0 < ballMargin a x
    · have hn := frontier_corner_radial_negative n m a hm x hx hs ht ha
      have hp : HasDerivAt (radialPath x) (x.1, 0) 1 := by
        convert ((hasDerivAt_id (1 : ℝ)).smul_const x.1).prodMk (hasDerivAt_const 1 x.2) using 1; simp [radialPath]
      have hf' : HasFDerivAt (defining n m a) (fderiv ℝ (defining n m a) x) (radialPath x 1) := by
        simpa [radialPath] using hf
      have hc := hf'.comp_hasDerivAt 1 hp
      intro hzero
      rw [hzero] at hc
      have hder := hc.deriv
      simp only [ContinuousLinearMap.zero_apply] at hder
      change deriv (fun v => defining n m a (radialPath x v)) 1 = 0 at hder
      linarith
    · have ht0 : ballMargin a x = 0 := le_antisymm (le_of_not_gt ht) hmargin.2.1
      have hn := frontier_edge_axial_nonzero n m a hm x hx (Or.inr ht0)
      have hp : HasDerivAt (axialPath x) (0, x.2) 1 := by
        convert (hasDerivAt_const (1 : ℝ) x.1).prodMk ((hasDerivAt_id (1 : ℝ)).mul_const x.2) using 1; simp [axialPath]
      have hf' : HasFDerivAt (defining n m a) (fderiv ℝ (defining n m a) x) (axialPath x 1) := by
        simpa [axialPath] using hf
      have hc := hf'.comp_hasDerivAt 1 hp
      intro hzero
      rw [hzero] at hc
      have hder := hc.deriv
      simp only [ContinuousLinearMap.zero_apply] at hder
      exact hn hder
  · have hs0 : coneMargin n m x = 0 := le_antisymm (le_of_not_gt hs) hmargin.1
    have hn := frontier_edge_axial_nonzero n m a hm x hx (Or.inl hs0)
    have hp : HasDerivAt (axialPath x) (0, x.2) 1 := by
      convert (hasDerivAt_const (1 : ℝ) x.1).prodMk ((hasDerivAt_id (1 : ℝ)).mul_const x.2) using 1; simp [axialPath]
    have hf' : HasFDerivAt (defining n m a) (fderiv ℝ (defining n m a) x) (axialPath x 1) := by
      simpa [axialPath] using hf
    have hc := hf'.comp_hasDerivAt 1 hp
    intro hzero
    rw [hzero] at hc
    have hder := hc.deriv
    simp only [ContinuousLinearMap.zero_apply] at hder
    exact hn hder

theorem frontier_local_level (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Point)
    (hx : x ∈ frontier (inclusion n m a)) :
    ∃ U : Set Point, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      (y ∈ inclusion n m a ↔ 0 < defining n m a y) := by
  have hs : Continuous (coneMargin n m) :=
    (continuous_abs.comp continuous_snd).sub ((ConicalSmoothCapGraph.cap_smooth n m hm).continuous.comp continuous_fst)
  have ht : Continuous (ballMargin a) :=
    (continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub (continuous_snd.pow 2)
  rcases frontier_one_margin_positive n m a hm x hx with hxS | hxT
  · refine ⟨{y | 0 < coneMargin n m y}, isOpen_lt continuous_const hs, hxS, ?_⟩
    intro y hy
    constructor
    · intro h
      exact sub_pos.mpr h.2.2
    · intro hf
      have hc := correction_nonnegative n (coneMargin n m y) (ballMargin a y)
      have hp : 0 < 2*coneMargin n m y*ballMargin a y := by
        dsimp [defining] at hf
        linarith
      have htpos : 0 < ballMargin a y := by
        by_contra h
        have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hy) (le_of_not_gt h)
        nlinarith
      exact ⟨hy, htpos, sub_pos.mp hf⟩
  · refine ⟨{y | 0 < ballMargin a y}, isOpen_lt continuous_const ht, hxT, ?_⟩
    intro y hy
    constructor
    · intro h
      exact sub_pos.mpr h.2.2
    · intro hf
      have hc := correction_nonnegative n (coneMargin n m y) (ballMargin a y)
      have hp : 0 < 2*coneMargin n m y*ballMargin a y := by
        dsimp [defining] at hf
        linarith
      have hspos : 0 < coneMargin n m y := by
        by_contra h
        have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (le_of_lt hy)
        nlinarith
      exact ⟨hspos, hy, sub_pos.mp hf⟩

end OQ14.ConicalJunctionInterface
#print axioms OQ14.ConicalJunctionInterface.corner_outside_cap_strict
#print axioms OQ14.ConicalJunctionInterface.frontier_nonzero_axial
#print axioms OQ14.ConicalJunctionInterface.frontier_margins
#print axioms OQ14.ConicalJunctionInterface.frontier_one_margin_positive
#print axioms OQ14.ConicalJunctionInterface.radial_path_deriv_negative
#print axioms OQ14.ConicalJunctionInterface.frontier_corner_radial_negative
#print axioms OQ14.ConicalJunctionInterface.frontier_edge_axial_nonzero
#print axioms OQ14.ConicalJunctionInterface.frontier_fderiv_nonzero
#print axioms OQ14.ConicalJunctionInterface.frontier_local_level

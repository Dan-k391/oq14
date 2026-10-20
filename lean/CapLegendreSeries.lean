import ConicalAngularTrial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-! Explicit convergent series for the regular-pole and odd Legendre solutions. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.CapLegendreSeries
open Set Filter
open scoped Topology

def poleCoeff (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => (((n : ℝ)*(n+1)-a)/(n+1)^2) * poleCoeff a n

def oddCoeff (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => ((((2*n+1 : ℕ) : ℝ)*(2*n+2)-a)/((2*n+2)*(2*n+3))) * oddCoeff a n

theorem poleCoeff_continuous (n : ℕ) : Continuous (fun a => poleCoeff a n) := by
  induction n with
  | zero => exact continuous_const
  | succ n hn => simpa only [poleCoeff] using
      (((continuous_const.sub continuous_id).div_const _).mul hn)

theorem oddCoeff_continuous (n : ℕ) : Continuous (fun a => oddCoeff a n) := by
  induction n with
  | zero => exact continuous_const
  | succ n hn => simpa only [oddCoeff] using
      (((continuous_const.sub continuous_id).div_const _).mul hn)

theorem poleCoeff_bound (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (n : ℕ) : |poleCoeff a n| ≤ 2 := by
  induction n with
  | zero => norm_num [poleCoeff]
  | succ n hn =>
    cases n with
    | zero => simpa [poleCoeff, abs_of_nonneg ha.1] using ha.2
    | succ n =>
      have hn0 : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hden : 0 < ((n+1 : ℕ) + 1 : ℝ)^2 := by positivity
      have hnum : 0 ≤ ((n+1 : ℕ) : ℝ)*((n+1 : ℕ)+1)-a := by nlinarith [ha.2]
      have hrat : 0 ≤ (((n+1 : ℕ) : ℝ)*((n+1 : ℕ)+1)-a)/((n+1 : ℕ)+1)^2 :=
        div_nonneg hnum hden.le
      have hle : (((n+1 : ℕ) : ℝ)*((n+1 : ℕ)+1)-a)/((n+1 : ℕ)+1)^2 ≤ 1 := by
        apply (div_le_iff₀ hden).mpr
        nlinarith [ha.1]
      rw [poleCoeff, abs_mul, abs_of_nonneg hrat]
      exact (mul_le_mul_of_nonneg_left hn hrat).trans (by nlinarith)

theorem oddCoeff_bound (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    0 ≤ oddCoeff a n ∧ oddCoeff a n ≤ 1 := by
  induction n with
  | zero => norm_num [oddCoeff]
  | succ n hn =>
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : 0 < (2*(n : ℝ)+2)*(2*n+3) := by positivity
    have hnum : 0 ≤ (2*(n : ℝ)+1)*(2*n+2)-a := by nlinarith [ha.2]
    have hr : 0 ≤ ((2*(n : ℝ)+1)*(2*n+2)-a)/((2*n+2)*(2*n+3)) :=
      div_nonneg hnum hden.le
    have hb : ((2*(n : ℝ)+1)*(2*n+2)-a)/((2*n+2)*(2*n+3)) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [ha.1]
    simp only [oddCoeff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    exact ⟨mul_nonneg hr hn.1, (mul_le_mul_of_nonneg_left hn.2 hr).trans (by linarith)⟩

def powerSum (c : ℕ → ℝ) (w : ℝ) : ℝ := ∑' n, c n * w ^ n
def pole (a z : ℝ) : ℝ := powerSum (poleCoeff a) ((1-z)/2)
def odd (a z : ℝ) : ℝ := z * powerSum (oddCoeff a) (z^2)

theorem power_summable (c : ℕ → ℝ) (C : ℝ) (hc : ∀ n, |c n| ≤ C)
    (w : ℝ) (hw : |w| < 1) : Summable (fun n => c n * w^n) := by
  apply Summable.of_norm_bounded (fun n => C * |w|^n)
    ((summable_geometric_of_lt_one (abs_nonneg w) hw).mul_left C)
  intro n
  simpa only [norm_mul, Real.norm_eq_abs, abs_pow] using
    mul_le_mul_of_nonneg_right (hc n) (pow_nonneg (abs_nonneg w) n)

theorem pole_summable (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    Summable (fun n => poleCoeff a n * ((1-z)/2)^n) :=
  power_summable _ 2 (poleCoeff_bound a ha) _ hz

theorem odd_summable (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    Summable (fun n => oddCoeff a n * (z^2)^n) := by
  refine power_summable _ 1 (fun n => ?_) _ ?_
  · rw [abs_of_nonneg (oddCoeff_bound a ha n).1]
    exact (oddCoeff_bound a ha n).2
  · rw [abs_of_nonneg (sq_nonneg z)]
    nlinarith [abs_nonneg z, sq_abs z]

theorem powerSum_parameter_continuousOn (c : ℝ → ℕ → ℝ) (C : ℝ)
    (hc : ∀ n, ContinuousOn (fun a => c a n) (Icc (0 : ℝ) 2))
    (hb : ∀ a ∈ Icc (0 : ℝ) 2, ∀ n, |c a n| ≤ C) (w : ℝ) (hw : |w| < 1) :
    ContinuousOn (fun a => powerSum (c a) w) (Icc (0 : ℝ) 2) := by
  apply continuousOn_tsum (u := fun n => C * |w|^n)
    (fun n => (hc n).mul continuousOn_const)
    ((summable_geometric_of_lt_one (abs_nonneg w) hw).mul_left C)
  intro n a ha
  simpa only [norm_mul, Real.norm_eq_abs, abs_pow] using
    mul_le_mul_of_nonneg_right (hb a ha n) (pow_nonneg (abs_nonneg w) n)

theorem pole_parameter_continuousOn (z : ℝ) (hz : |(1-z)/2| < 1) :
    ContinuousOn (fun a => pole a z) (Icc (0 : ℝ) 2) :=
  powerSum_parameter_continuousOn poleCoeff 2 (fun n => (poleCoeff_continuous n).continuousOn)
    poleCoeff_bound _ hz

theorem odd_parameter_continuousOn (z : ℝ) (hz : |z| < 1) :
    ContinuousOn (fun a => odd a z) (Icc (0 : ℝ) 2) := by
  apply continuousOn_const.mul
  refine powerSum_parameter_continuousOn oddCoeff 1
    (fun n => (oddCoeff_continuous n).continuousOn) (fun a ha n => ?_) _ ?_
  · rw [abs_of_nonneg (oddCoeff_bound a ha n).1]
    exact (oddCoeff_bound a ha n).2
  · rw [abs_of_nonneg (sq_nonneg z)]
    nlinarith [abs_nonneg z, sq_abs z]

def derivativeCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ := (n+1) * c (n+1)

theorem geometric_succ_summable (k : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n+1 : ℝ)^k * r^n) := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one (r := r) k
    (by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr1)).comp_injective Nat.succ_injective
  convert h.div_const r using 1
  funext n
  dsimp only [Function.comp_def, Nat.succ_eq_add_one]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem power_summable_growth (c : ℕ → ℝ) (C : ℝ) (k : ℕ)
    (hc : ∀ n, |c n| ≤ C * (n+1)^k) (w : ℝ) (hw : |w| < 1) :
    Summable (fun n => c n * w^n) := by
  by_cases hz : w = 0
  · subst w
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  · have hp : 0 < |w| := abs_pos.mpr hz
    apply Summable.of_norm_bounded (fun n : ℕ => C*(n+1)^k * |w|^n)
      (by simpa only [mul_assoc] using (geometric_succ_summable k |w| hp hw).mul_left C)
    intro n
    simpa only [norm_mul, Real.norm_eq_abs, abs_pow] using
      mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hp.le n)

theorem derivativeCoeff_growth (c : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hc : ∀ n, |c n| ≤ C * (n+1)^k) (n : ℕ) :
    |derivativeCoeff c n| ≤ (C*2^k) * (n+1)^(k+1) := by
  have hn : 0 ≤ (n+1 : ℝ) := by positivity
  have hp : ((n+1 : ℕ) + 1 : ℝ)^k ≤ (2*(n+1 : ℝ))^k := by
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  rw [derivativeCoeff, abs_mul, abs_of_nonneg hn]
  calc
    _ ≤ (n+1 : ℝ)*(C*((n+1 : ℕ)+1)^k) := mul_le_mul_of_nonneg_left (hc (n+1)) hn
    _ ≤ (n+1 : ℝ)*(C*(2*(n+1 : ℝ))^k) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) hn
    _ = (C*2^k)*(n+1 : ℝ)^(k+1) := by rw [mul_pow, pow_succ]; ring

theorem powerSum_hasDerivAt_growth (c : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hc : ∀ n, |c n| ≤ C*(n+1)^k) (w : ℝ) (hw : |w| < 1) :
    HasDerivAt (powerSum c) (powerSum (derivativeCoeff c) w) w := by
  let r := (|w|+1)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hwr : |w| < r := by dsimp [r]; linarith
  have hsum := geometric_succ_summable (k+1) r hr hr1
  have hbound (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (-r) r) :
      |derivativeCoeff c n * x^n| ≤ (C*2^k)*(n+1)^(k+1)*r^n := by
    rw [abs_mul, abs_pow]
    apply mul_le_mul (derivativeCoeff_growth c C hC k hc n)
      (pow_le_pow_left₀ (abs_nonneg x) (le_of_lt (abs_lt.mpr hx)) n)
      (pow_nonneg (abs_nonneg x) n) (by positivity)
  have hd : HasDerivAt (fun x => ∑' n : ℕ, c (n+1)*x^(n+1))
      (powerSum (derivativeCoeff c) w) w := by
    change HasDerivAt (fun x => ∑' n : ℕ, c (n+1)*x^(n+1))
      (∑' n, derivativeCoeff c n * w^n) w
    apply hasDerivAt_tsum_of_isPreconnected
      (g' := fun n x => derivativeCoeff c n * x^n)
      (u := fun n : ℕ => (C*2^k)*(n+1)^(k+1)*r^n)
      (by simpa only [mul_assoc] using hsum.mul_left (C*2^k))
      isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    · intro n x _
      convert ((hasDerivAt_id x).pow (n+1)).const_mul (c (n+1)) using 1
      simp only [derivativeCoeff, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        mul_one]
      dsimp only [id_eq]
      ring
    · intro n x hx
      simpa only [Real.norm_eq_abs] using hbound n x hx
    · exact (mem_Ioo.mpr ⟨neg_lt_zero.mpr hr, hr⟩ : (0 : ℝ) ∈ Ioo (-r) r)
    · simp only [zero_pow (Nat.succ_ne_zero _), mul_zero, summable_zero]
    · exact abs_lt.mp hwr
  apply hd.const_add (c 0) |>.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hwr).1 (abs_lt.mp hwr).2] with x hx
  have hxs : |x| < 1 := (abs_lt.mpr hx).trans hr1
  simpa only [powerSum, pow_zero, mul_one] using
    (power_summable_growth c C k hc x hxs).tsum_eq_zero_add

def momentCoeff (c : ℕ → ℝ) (j n : ℕ) : ℝ := (n : ℝ)^j * c n

theorem momentCoeff_growth (c : ℕ → ℝ) (C : ℝ) (_hC : 0 ≤ C) (k j : ℕ)
    (hc : ∀ n, |c n| ≤ C*(n+1)^k) (n : ℕ) :
    |momentCoeff c j n| ≤ C*(n+1)^(k+j) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [momentCoeff, abs_mul, abs_pow, abs_of_nonneg hn]
  calc
    _ ≤ (n+1 : ℝ)^j * (C*(n+1)^k) := mul_le_mul
      (pow_le_pow_left₀ hn (by linarith) j) (hc n) (abs_nonneg _) (by positivity)
    _ = C*(n+1 : ℝ)^(k+j) := by rw [pow_add]; ring

theorem first_moment (c : ℕ → ℝ) (w : ℝ)
    (hm : Summable (fun n : ℕ => (n : ℝ)*c n*w^n)) :
    powerSum (momentCoeff c 1) w = w * powerSum (derivativeCoeff c) w := by
  change (∑' n : ℕ, (n : ℝ)^1*c n*w^n) = _
  simp only [pow_one]
  rw [hm.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [powerSum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp only [derivativeCoeff]
  push_cast
  rw [pow_succ]
  ring

theorem second_moment (c : ℕ → ℝ) (w : ℝ)
    (hm : Summable (fun n : ℕ => (n : ℝ)^2*c n*w^n))
    (hd : Summable (fun n : ℕ => derivativeCoeff c n*w^n))
    (hmd : Summable (fun n : ℕ => (n : ℝ)*derivativeCoeff c n*w^n)) :
    powerSum (momentCoeff c 2) w =
      w^2 * powerSum (derivativeCoeff (derivativeCoeff c)) w +
      w * powerSum (derivativeCoeff c) w := by
  have he : powerSum (momentCoeff c 2) w =
      w*(powerSum (momentCoeff (derivativeCoeff c) 1) w + powerSum (derivativeCoeff c) w) := by
    change (∑' n : ℕ, (n : ℝ)^2*c n*w^n) = _
    rw [hm.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, zero_add]
    unfold powerSum
    rw [← Summable.tsum_add (by simpa only [momentCoeff, pow_one] using hmd) hd, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [momentCoeff, derivativeCoeff]
    push_cast
    rw [pow_succ]
    ring
  rw [he, first_moment _ _ hmd]
  ring

theorem recurrence_power_ode (c : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hc : ∀ n, |c n| ≤ C*(n+1)^k) (B s p w : ℝ) (hw : |w| < 1)
    (hr : ∀ n : ℕ, (n+1 : ℝ)*(n+B)*c (n+1) =
      ((n : ℝ)^2+s*n+p)*c n) :
    w*(1-w)*powerSum (derivativeCoeff (derivativeCoeff c)) w +
      (B-(s+1)*w)*powerSum (derivativeCoeff c) w - p*powerSum c w = 0 := by
  have hs0 := power_summable_growth c C k hc w hw
  have hs1 := power_summable_growth _ C (k+1) (momentCoeff_growth c C hC k 1 hc) w hw
  have hs2 := power_summable_growth _ C (k+2) (momentCoeff_growth c C hC k 2 hc) w hw
  have hd0 := power_summable_growth _ (C*2^k) (k+1) (derivativeCoeff_growth c C hC k hc) w hw
  have hd1 := power_summable_growth _ (C*2^k) (k+1+1)
    (momentCoeff_growth _ _ (by positivity) (k+1) 1 (derivativeCoeff_growth c C hC k hc)) w hw
  simp only [momentCoeff, pow_one] at hs1 hs2 hd1
  have he : ∀ n : ℕ,
      (n : ℝ)*derivativeCoeff c n*w^n + B*(derivativeCoeff c n*w^n) =
        (n : ℝ)^2*c n*w^n + s*((n : ℝ)*c n*w^n) + p*(c n*w^n) := by
    intro n
    dsimp only [derivativeCoeff]
    linear_combination (hr n)*w^n
  have ht := tsum_congr he
  rw [hd1.tsum_add (hd0.mul_left B),
    (hs2.add (hs1.mul_left s)).tsum_add (hs0.mul_left p),
    hs2.tsum_add (hs1.mul_left s)] at ht
  simp only [tsum_mul_left] at ht
  have ht' : powerSum (momentCoeff (derivativeCoeff c) 1) w + B*powerSum (derivativeCoeff c) w =
      powerSum (momentCoeff c 2) w + s*powerSum (momentCoeff c 1) w + p*powerSum c w := by
    simpa only [powerSum, momentCoeff, pow_one] using ht
  rw [first_moment _ _ hd1, first_moment _ _ hs1, second_moment _ _ hs2 hd0 hd1] at ht'
  nlinarith [ht']

theorem poleCoeff_growth (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    |poleCoeff a n| ≤ 2*(n+1)^0 := by simpa using poleCoeff_bound a ha n

theorem oddCoeff_growth (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (n : ℕ) :
    |oddCoeff a n| ≤ 1*(n+1)^0 := by
  simpa [abs_of_nonneg (oddCoeff_bound a ha n).1] using (oddCoeff_bound a ha n).2

def poleD (a z : ℝ) : ℝ := (-1/2) * powerSum (derivativeCoeff (poleCoeff a)) ((1-z)/2)
def poleDD (a z : ℝ) : ℝ := (1/4) * powerSum (derivativeCoeff (derivativeCoeff (poleCoeff a))) ((1-z)/2)
def oddD (a z : ℝ) : ℝ := powerSum (oddCoeff a) (z^2) +
  2*z^2*powerSum (derivativeCoeff (oddCoeff a)) (z^2)
def oddDD (a z : ℝ) : ℝ := 6*z*powerSum (derivativeCoeff (oddCoeff a)) (z^2) +
  4*z^3*powerSum (derivativeCoeff (derivativeCoeff (oddCoeff a))) (z^2)

theorem pole_hasDerivAt (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    HasDerivAt (pole a) (poleD a z) z := by
  have h := (powerSum_hasDerivAt_growth _ 2 (by norm_num) 0
    (poleCoeff_growth a ha) _ hz).comp (h := fun y : ℝ => (1-y)/2) z
    (((hasDerivAt_id z).const_sub 1).div_const 2)
  convert h using 1
  simp only [poleD]
  ring

theorem poleD_hasDerivAt (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    HasDerivAt (poleD a) (poleDD a z) z := by
  have h := ((powerSum_hasDerivAt_growth _ (2*2^0) (by norm_num) (0+1)
    (derivativeCoeff_growth _ 2 (by norm_num) 0 (poleCoeff_growth a ha)) _ hz).comp
    (h := fun y : ℝ => (1-y)/2) z
    (((hasDerivAt_id z).const_sub 1).div_const 2)).const_mul (-1/2)
  convert h using 1
  simp only [poleDD]
  ring

theorem odd_argument (z : ℝ) (hz : |z| < 1) : |z^2| < 1 := by
  rw [abs_of_nonneg (sq_nonneg z)]
  nlinarith [abs_nonneg z, sq_abs z]

theorem odd_hasDerivAt (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    HasDerivAt (odd a) (oddD a z) z := by
  have h := (powerSum_hasDerivAt_growth _ 1 (by norm_num) 0 (oddCoeff_growth a ha)
    _ (odd_argument z hz)).comp (h := fun y : ℝ => y^2) z ((hasDerivAt_id z).pow 2)
  convert (hasDerivAt_id z).mul h using 1
  simp only [oddD, id_eq, Function.comp_apply]
  norm_num
  ring

theorem oddD_hasDerivAt (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    HasDerivAt (oddD a) (oddDD a z) z := by
  have hy := (powerSum_hasDerivAt_growth _ 1 (by norm_num) 0 (oddCoeff_growth a ha)
    _ (odd_argument z hz)).comp (h := fun y : ℝ => y^2) z ((hasDerivAt_id z).pow 2)
  have hd := (powerSum_hasDerivAt_growth _ (1*2^0) (by norm_num) (0+1)
    (derivativeCoeff_growth _ 1 (by norm_num) 0 (oddCoeff_growth a ha))
    _ (odd_argument z hz)).comp (h := fun y : ℝ => y^2) z ((hasDerivAt_id z).pow 2)
  have h := hy.add ((((hasDerivAt_id z).pow 2).const_mul 2).mul hd)
  convert h using 1
  simp only [oddDD, id_eq, Function.comp_apply]
  norm_num
  ring

theorem pole_legendre (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    (1-z^2)*poleDD a z - 2*z*poleD a z + a*pole a z = 0 := by
  have h := recurrence_power_ode (poleCoeff a) 2 (by norm_num) 0 (poleCoeff_growth a ha)
    1 1 (-a) ((1-z)/2) hz (by
      intro n
      rw [poleCoeff]
      have hn : (n+1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring)
  dsimp only [pole, poleD, poleDD]
  linear_combination h

theorem odd_legendre (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    (1-z^2)*oddDD a z - 2*z*oddD a z + a*odd a z = 0 := by
  have h := recurrence_power_ode (oddCoeff a) 1 (by norm_num) 0 (oddCoeff_growth a ha)
    (3/2) (3/2) (1/2-a/4) (z^2) (odd_argument z hz) (by
      intro n
      rw [oddCoeff]
      push_cast
      have hn : (2*(n : ℝ)+2) ≠ 0 := by positivity
      have hn' : (2*(n : ℝ)+3) ≠ 0 := by positivity
      field_simp
      ring)
  dsimp only [odd, oddD, oddDD]
  linear_combination 4*z*h

theorem powerSum_parameter_continuousOn_growth (c : ℝ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hc : ∀ n, ContinuousOn (fun a => c a n) (Icc (0 : ℝ) 2))
    (hb : ∀ a ∈ Icc (0 : ℝ) 2, ∀ n, |c a n| ≤ C*(n+1)^k) (w : ℝ) (hw : |w| < 1) :
    ContinuousOn (fun a => powerSum (c a) w) (Icc (0 : ℝ) 2) := by
  let r := (|w|+1)/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hwr : |w| ≤ r := by dsimp [r]; linarith
  apply continuousOn_tsum (u := fun n : ℕ => C*(n+1)^k*r^n)
    (fun n => (hc n).mul continuousOn_const)
    (by simpa only [mul_assoc] using (geometric_succ_summable k r hr hr1).mul_left C)
  intro n a ha
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul (hb a ha n) (pow_le_pow_left₀ (abs_nonneg w) hwr n)
    (pow_nonneg (abs_nonneg w) n) (by positivity)

theorem derivativeCoeff_continuous (c : ℝ → ℕ → ℝ)
    (hc : ∀ n, Continuous (fun a => c a n)) (n : ℕ) :
    Continuous (fun a => derivativeCoeff (c a) n) := continuous_const.mul (hc (n+1))

theorem poleD_parameter_continuousOn (z : ℝ) (hz : |(1-z)/2| < 1) :
    ContinuousOn (fun a => poleD a z) (Icc (0 : ℝ) 2) := by
  apply continuousOn_const.mul
  exact powerSum_parameter_continuousOn_growth _ (2*2^0) (by norm_num) (0+1)
    (fun n => (derivativeCoeff_continuous poleCoeff poleCoeff_continuous n).continuousOn)
    (fun a ha n => derivativeCoeff_growth _ 2 (by norm_num) 0 (poleCoeff_growth a ha) n) _ hz

theorem oddD_parameter_continuousOn (z : ℝ) (hz : |z| < 1) :
    ContinuousOn (fun a => oddD a z) (Icc (0 : ℝ) 2) := by
  apply ContinuousOn.add
  · exact powerSum_parameter_continuousOn oddCoeff 1
      (fun n => (oddCoeff_continuous n).continuousOn)
      (fun a ha n => by simpa using oddCoeff_growth a ha n) _ (odd_argument z hz)
  · apply continuousOn_const.mul
    exact powerSum_parameter_continuousOn_growth _ (1*2^0) (by norm_num) (0+1)
      (fun n => (derivativeCoeff_continuous oddCoeff oddCoeff_continuous n).continuousOn)
      (fun a ha n => derivativeCoeff_growth _ 1 (by norm_num) 0 (oddCoeff_growth a ha) n)
      _ (odd_argument z hz)

theorem poleCoeff_zero (n : ℕ) : poleCoeff 0 (n+1) = 0 := by
  induction n with
  | zero => norm_num [poleCoeff]
  | succ n hn => rw [poleCoeff, hn, mul_zero]

theorem poleCoeff_two (n : ℕ) : poleCoeff 2 (n+2) = 0 := by
  induction n with
  | zero => norm_num [poleCoeff]
  | succ n hn => rw [poleCoeff, hn, mul_zero]

theorem oddCoeff_two (n : ℕ) : oddCoeff 2 (n+1) = 0 := by
  induction n with
  | zero => norm_num [oddCoeff]
  | succ n hn => rw [oddCoeff, hn, mul_zero]

theorem powerSum_constant (c : ℕ → ℝ) (hc : ∀ n, c (n+1) = 0) (w : ℝ) :
    powerSum c w = c 0 := by
  rw [powerSum, tsum_eq_single 0]
  · simp
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [hc]

theorem pole_zero (z : ℝ) : pole 0 z = 1 := by
  rw [pole, powerSum_constant _ poleCoeff_zero]
  rfl

theorem poleD_zero (z : ℝ) : poleD 0 z = 0 := by
  simp [poleD, powerSum, derivativeCoeff, poleCoeff_zero]

theorem odd_two (z : ℝ) : odd 2 z = z := by
  rw [odd, powerSum_constant _ oddCoeff_two]
  simp [oddCoeff]

theorem oddD_two (z : ℝ) : oddD 2 z = 1 := by
  have hd : derivativeCoeff (oddCoeff 2) = 0 := by
    funext n
    simp only [derivativeCoeff, oddCoeff_two, mul_zero, Pi.zero_apply]
  rw [oddD, powerSum_constant _ oddCoeff_two]
  rw [hd]
  simp [oddCoeff, powerSum]

theorem pole_two (z : ℝ) : pole 2 z = z := by
  rw [pole, powerSum, tsum_eq_sum (s := {0,1})]
  · norm_num [poleCoeff]
    ring
  · intro n hn
    have hn2 : 2 ≤ n := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn; omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn2
    rw [hm, show 2+m=m+2 by omega, poleCoeff_two, zero_mul]

theorem poleD_two (z : ℝ) : poleD 2 z = 1 := by
  have he : derivativeCoeff (poleCoeff 2) = fun n : ℕ => if n = 0 then -2 else 0 := by
    funext n
    cases n with
    | zero => norm_num [derivativeCoeff, poleCoeff]
    | succ n => simp [derivativeCoeff, show n+1+1=n+2 by omega, poleCoeff_two]
  rw [poleD, powerSum_constant _ (by intro n; rw [he]; simp)]
  norm_num [he]

theorem odd_powerSum_ge_one (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    1 ≤ powerSum (oddCoeff a) (z^2) := by
  have hs := odd_summable a z ha hz
  have h := hs.le_tsum 0 (fun n _ => mul_nonneg (oddCoeff_bound a ha n).1 (by positivity))
  simpa only [powerSum, oddCoeff, pow_zero, mul_one] using h

theorem odd_positive (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : 0 < z) (hz1 : z < 1) :
    0 < odd a z := by
  have hp := odd_powerSum_ge_one a z ha (by rw [abs_of_pos hz]; exact hz1)
  exact mul_pos hz (by linarith)

theorem oddD_ge_one (a z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    1 ≤ oddD a z := by
  have hp := odd_powerSum_ge_one a z ha hz
  have hd : 0 ≤ powerSum (derivativeCoeff (oddCoeff a)) (z^2) := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg (mul_nonneg (by positivity) (oddCoeff_bound a ha (n+1)).1) (by positivity)
  dsimp only [oddD]
  nlinarith [sq_nonneg z]

theorem pole_at_one (a : ℝ) : pole a 1 = 1 := by
  unfold pole powerSum
  norm_num only [sub_self, zero_div]
  rw [tsum_eq_single 0]
  · simp [poleCoeff]
  · intro n hn
    simp [zero_pow hn]

end OQ14.CapLegendreSeries

#print axioms OQ14.CapLegendreSeries.poleCoeff_continuous
#print axioms OQ14.CapLegendreSeries.oddCoeff_continuous
#print axioms OQ14.CapLegendreSeries.poleCoeff_bound
#print axioms OQ14.CapLegendreSeries.oddCoeff_bound
#print axioms OQ14.CapLegendreSeries.power_summable
#print axioms OQ14.CapLegendreSeries.pole_summable
#print axioms OQ14.CapLegendreSeries.odd_summable
#print axioms OQ14.CapLegendreSeries.powerSum_parameter_continuousOn
#print axioms OQ14.CapLegendreSeries.pole_parameter_continuousOn
#print axioms OQ14.CapLegendreSeries.odd_parameter_continuousOn
#print axioms OQ14.CapLegendreSeries.geometric_succ_summable
#print axioms OQ14.CapLegendreSeries.power_summable_growth
#print axioms OQ14.CapLegendreSeries.derivativeCoeff_growth
#print axioms OQ14.CapLegendreSeries.powerSum_hasDerivAt_growth
#print axioms OQ14.CapLegendreSeries.momentCoeff_growth
#print axioms OQ14.CapLegendreSeries.first_moment
#print axioms OQ14.CapLegendreSeries.second_moment
#print axioms OQ14.CapLegendreSeries.recurrence_power_ode
#print axioms OQ14.CapLegendreSeries.poleCoeff_growth
#print axioms OQ14.CapLegendreSeries.oddCoeff_growth
#print axioms OQ14.CapLegendreSeries.pole_hasDerivAt
#print axioms OQ14.CapLegendreSeries.poleD_hasDerivAt
#print axioms OQ14.CapLegendreSeries.odd_argument
#print axioms OQ14.CapLegendreSeries.odd_hasDerivAt
#print axioms OQ14.CapLegendreSeries.oddD_hasDerivAt
#print axioms OQ14.CapLegendreSeries.pole_legendre
#print axioms OQ14.CapLegendreSeries.odd_legendre
#print axioms OQ14.CapLegendreSeries.powerSum_parameter_continuousOn_growth
#print axioms OQ14.CapLegendreSeries.derivativeCoeff_continuous
#print axioms OQ14.CapLegendreSeries.poleD_parameter_continuousOn
#print axioms OQ14.CapLegendreSeries.oddD_parameter_continuousOn
#print axioms OQ14.CapLegendreSeries.poleCoeff_zero
#print axioms OQ14.CapLegendreSeries.poleCoeff_two
#print axioms OQ14.CapLegendreSeries.oddCoeff_two
#print axioms OQ14.CapLegendreSeries.powerSum_constant
#print axioms OQ14.CapLegendreSeries.pole_zero
#print axioms OQ14.CapLegendreSeries.poleD_zero
#print axioms OQ14.CapLegendreSeries.odd_two
#print axioms OQ14.CapLegendreSeries.oddD_two
#print axioms OQ14.CapLegendreSeries.pole_two
#print axioms OQ14.CapLegendreSeries.poleD_two
#print axioms OQ14.CapLegendreSeries.odd_powerSum_ge_one
#print axioms OQ14.CapLegendreSeries.odd_positive
#print axioms OQ14.CapLegendreSeries.oddD_ge_one
#print axioms OQ14.CapLegendreSeries.pole_at_one

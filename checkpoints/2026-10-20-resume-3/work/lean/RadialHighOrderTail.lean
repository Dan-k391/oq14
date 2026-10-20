import RadialHighOrderBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Genuine polynomially weighted high-order reaction tails -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialHighOrderTail

open Filter Set Metric OQ14.HankelRealBasis OQ14.RadialHighOrderBound
open scoped Topology

def majorant (l : ℕ) (s R : ℝ) : ℝ :=
  4*Real.exp (3*R/2)*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1))

theorem radius_ratio_bounds (s R : ℝ) (_hs : 0 ≤ s) (hR : 0 < R)
    (hthreshold : Real.exp 1*s ≤ R) : s/R ≤ Real.exp (-1) ∧ s/R ≤ 1/2 := by
  have he : Real.exp (-1)*Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_le_mul_of_nonneg_left hthreshold (Real.exp_pos (-1)).le
  rw [← mul_assoc,he,one_mul] at hm
  have hratio : s/R ≤ Real.exp (-1) := (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hm)
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
  have hhalf : Real.exp (-1) ≤ (1 : ℝ)/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using div_le_div_of_nonneg_left zero_le_one (by norm_num : (0 : ℝ) < 2) hexp
  exact ⟨hratio,hratio.trans hhalf⟩

theorem exponential_ratio_bound (l : ℕ) (s R : ℝ) (hs : 0 ≤ s) (hR : 0 < R)
    (hthreshold : Real.exp 1*s ≤ R) (hl : 2*R ≤ l) :
    Real.exp (3*R/2)*(s/R)^l ≤ Real.exp (-R/2) := by
  have hpow := pow_le_pow_left₀ (div_nonneg hs hR.le) (radius_ratio_bounds s R hs hR hthreshold).1 l
  have he : (Real.exp (-1))^l = Real.exp (-(l : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hpow
  apply (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem majorant_factor (l : ℕ) (s R : ℝ) (hR : R ≠ 0) :
    majorant l s R = (4*s^2/(R*(2*l+1 : ℝ)))*(Real.exp (3*R/2)*(s/R)^l)*(s/R)^l := by
  unfold majorant
  rw [show 2*l+2=l+l+2 by omega,show 2*l+1=l+l+1 by omega]
  simp only [pow_add,pow_one,pow_two,div_pow]
  field_simp [hR]
  ring

theorem majorant_geometric_envelope (l : ℕ) (s R : ℝ) (hs : 0 ≤ s) (hR : 1 ≤ R)
    (hthreshold : Real.exp 1*s ≤ R) (hl : 2*R ≤ l) :
    majorant l s R ≤ 4*s^2*Real.exp (-R/2)*(1/2 : ℝ)^l := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hden : 1 ≤ R*(2*l+1 : ℝ) := by
    nlinarith [mul_nonneg hRp.le (Nat.cast_nonneg (α := ℝ) l)]
  have hpre : 4*s^2/(R*(2*l+1 : ℝ)) ≤ 4*s^2 := by
    apply (div_le_iff₀ (by positivity : 0 < R*(2*l+1 : ℝ))).mpr
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hden)]
  have hscaled := exponential_ratio_bound l s R hs hRp hthreshold hl
  have hpow := pow_le_pow_left₀ (div_nonneg hs hRp.le) (radius_ratio_bounds s R hs hRp hthreshold).2 l
  rw [majorant_factor l s R hRp.ne']
  exact mul_le_mul (mul_le_mul hpre hscaled (by positivity) (by positivity)) hpow
    (by positivity) (by positivity)

theorem polynomial_geometric_summable (k : ℕ) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*(1/2 : ℝ)^l) := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one (r := (1/2 : ℝ)) k (by norm_num)).comp_injective
    Nat.succ_injective
  convert h.mul_left (2 : ℝ) using 1
  funext l
  dsimp only [Function.comp_def,Nat.succ_eq_add_one]
  push_cast
  rw [pow_succ]
  ring

def reactionTerm (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ) (C s R : ℝ) (l : ℕ) : ℝ :=
  if hR : 0 < R then
    if C*R ≤ l then ‖RadialSource.gamma l (gs R) R (X R) hR‖*(regular l s)^2 else 0
  else 0

def weightedTail (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ) (C s : ℝ) (k : ℕ) (R : ℝ) : ℝ :=
  ∑' l : ℕ, (l+1 : ℝ)^k*reactionTerm gs X C s R l

theorem reactionTerm_nonnegative (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s R : ℝ) (l : ℕ) : 0 ≤ reactionTerm gs X C s R l := by
  unfold reactionTerm
  split_ifs <;> positivity

theorem reactionTerm_envelope (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s R : ℝ) (hC : 2 ≤ C) (hs : 0 < s) (hR : 1 ≤ R)
    (hthreshold : Real.exp 1*s ≤ R) (hX : 0 < X R)
    (hstack : ∀ l : ℕ, C*R ≤ l → ∀ g ∈ gs R, g.q^2*g.b^2 ≤ HankelEnergy.angular l)
    (l : ℕ) : reactionTerm gs X C s R l ≤ 4*s^2*Real.exp (-R/2)*(1/2 : ℝ)^l := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [reactionTerm,dif_pos hRp]
  split_ifs with hl
  · have hhigh : 2*R ≤ l := (mul_le_mul_of_nonneg_right hC hRp.le).trans hl
    have hsR : s ≤ R := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
      nlinarith
    exact (actual_reaction_high_order l (gs R) R (X R) s hRp hX hs hsR hhigh (hstack l hl)).trans
      (majorant_geometric_envelope l s R hs.le hR hthreshold hhigh)
  · positivity

def geometricWeight (k : ℕ) : ℝ := ∑' l : ℕ, (l+1 : ℝ)^k*(1/2 : ℝ)^l

theorem weightedTail_nonnegative (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s : ℝ) (k : ℕ) (R : ℝ) : 0 ≤ weightedTail gs X C s k R := by
  exact tsum_nonneg (fun l => mul_nonneg (by positivity) (reactionTerm_nonnegative gs X C s R l))

theorem weighted_reaction_summable (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s R : ℝ) (k : ℕ) (hC : 2 ≤ C) (hs : 0 < s) (hR : 1 ≤ R)
    (hthreshold : Real.exp 1*s ≤ R) (hX : 0 < X R)
    (hstack : ∀ l : ℕ, C*R ≤ l → ∀ g ∈ gs R, g.q^2*g.b^2 ≤ HankelEnergy.angular l) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*reactionTerm gs X C s R l) := by
  apply Summable.of_nonneg_of_le
    (fun l => mul_nonneg (by positivity) (reactionTerm_nonnegative gs X C s R l))
    (fun l => ?_) ((polynomial_geometric_summable k).mul_left (4*s^2*Real.exp (-R/2)))
  calc
    _ ≤ (l+1 : ℝ)^k*(4*s^2*Real.exp (-R/2)*(1/2 : ℝ)^l) :=
      mul_le_mul_of_nonneg_left (reactionTerm_envelope gs X C s R hC hs hR hthreshold hX hstack l)
        (by positivity)
    _ = _ := by ring

theorem weightedTail_le (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s R : ℝ) (k : ℕ) (hC : 2 ≤ C) (hs : 0 < s) (hR : 1 ≤ R)
    (hthreshold : Real.exp 1*s ≤ R) (hX : 0 < X R)
    (hstack : ∀ l : ℕ, C*R ≤ l → ∀ g ∈ gs R, g.q^2*g.b^2 ≤ HankelEnergy.angular l) :
    weightedTail gs X C s k R ≤ 4*s^2*Real.exp (-R/2)*geometricWeight k := by
  have hb := (polynomial_geometric_summable k).mul_left (4*s^2*Real.exp (-R/2))
  rw [weightedTail,geometricWeight,← tsum_mul_left]
  apply (weighted_reaction_summable gs X C s R k hC hs hR hthreshold hX hstack).tsum_le_tsum _ hb
  intro l
  calc
    _ ≤ (l+1 : ℝ)^k*(4*s^2*Real.exp (-R/2)*(1/2 : ℝ)^l) :=
      mul_le_mul_of_nonneg_left (reactionTerm_envelope gs X C s R hC hs hR hthreshold hX hstack l)
        (by positivity)
    _ = _ := by ring

theorem weightedTail_decay (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s : ℝ) (k N : ℕ) (hC : 2 ≤ C) (hs : 0 < s)
    (hX : ∀ R, 1 ≤ R → 0 < X R)
    (hstack : ∀ R, 1 ≤ R → ∀ l : ℕ, C*R ≤ l →
      ∀ g ∈ gs R, g.q^2*g.b^2 ≤ HankelEnergy.angular l) :
    Tendsto (fun R : ℝ => R^N*weightedTail gs X C s k R) atTop (𝓝 0) := by
  have he : Tendsto (fun R : ℝ => R^N*Real.exp (-R/2)) atTop (𝓝 0) := by
    convert tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N : ℝ) (1/2) (by norm_num) using 1
    simp only [Real.rpow_natCast]
    congr 1
    funext R
    congr 2
    ring
  have he' := he.mul_const (4*s^2*geometricWeight k)
  simp only [zero_mul] at he'
  apply squeeze_zero' _ _ he'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact mul_nonneg (pow_nonneg (zero_lt_one.trans_le hR).le _) (weightedTail_nonnegative gs X C s k R)
  · filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_ge_atTop (Real.exp 1*s)] with R hR ht
    calc
      _ ≤ R^N*(4*s^2*Real.exp (-R/2)*geometricWeight k) :=
        mul_le_mul_of_nonneg_left (weightedTail_le gs X C s R k hC hs hR ht (hX R hR) (hstack R hR))
          (pow_nonneg (zero_lt_one.trans_le hR).le _)
      _ = _ := by ring

theorem weightedTail_tendsto_zero (gs : ℝ → List RadialStack.Layer) (X : ℝ → ℝ)
    (C s : ℝ) (k : ℕ) (hC : 2 ≤ C) (hs : 0 < s)
    (hX : ∀ R, 1 ≤ R → 0 < X R)
    (hstack : ∀ R, 1 ≤ R → ∀ l : ℕ, C*R ≤ l →
      ∀ g ∈ gs R, g.q^2*g.b^2 ≤ HankelEnergy.angular l) :
    Tendsto (weightedTail gs X C s k) atTop (𝓝 0) := by
  simpa only [pow_zero,one_mul] using weightedTail_decay gs X C s k 0 hC hs hX hstack

end OQ14.RadialHighOrderTail



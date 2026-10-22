import RadialReactionKernel

/-! Absolute scalar reaction tails for first mixed derivatives on compact annuli. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialReactionTail

open Filter Set OQ14.RadialStack OQ14.RadialHighOrderTail OQ14.RadialReactionKernel
open scoped Topology

def componentTerm (gs : ℝ → List Layer) (X : ℝ → ℝ) (C R : ℝ)
    (d e : Bool) (x y : ℝ) (l : ℕ) : ℂ :=
  if hR : 0 < R then
    if C*R ≤ l then derivativeComponent l (gs R) R (X R) hR d e x y else 0
  else 0

def normTail (gs : ℝ → List Layer) (X : ℝ → ℝ) (C : ℝ) (k : ℕ)
    (R : ℝ) (d e : Bool) (x y : ℝ) : ℝ :=
  ∑' l : ℕ, (l+1 : ℝ)^k*‖componentTerm gs X C R d e x y l‖

theorem componentTerm_norm_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (C R a s x y : ℝ) (d e : Bool) (hC : 2 ≤ C) (hR : 0 < R)
    (ha : 0 < a) (hx : x ∈ Icc a s) (hy : y ∈ Icc a s) (hsR : s ≤ R) (l : ℕ) :
    ‖componentTerm gs X C R d e x y l‖ ≤
      gapConstant a^2*(l+1 : ℝ)^2*reactionTerm gs X C s R l := by
  rw [componentTerm,reactionTerm,dif_pos hR,dif_pos hR]
  split_ifs with hl
  · have hh : 2*R ≤ l := (mul_le_mul_of_nonneg_right hC hR.le).trans hl
    exact component_norm_bound l (gs R) R (X R) a s x y hR d e
      (RadialHighOrderBound.high_order_barrier l R hR hh) ha hx hy hsR
  · simp

theorem weighted_component_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (C R a s x y : ℝ) (k : ℕ) (d e : Bool) (hC : 2 ≤ C) (hR : 0 < R)
    (ha : 0 < a) (hx : x ∈ Icc a s) (hy : y ∈ Icc a s) (hsR : s ≤ R) (l : ℕ) :
    (l+1 : ℝ)^k*‖componentTerm gs X C R d e x y l‖ ≤
      gapConstant a^2*((l+1 : ℝ)^(k+2)*reactionTerm gs X C s R l) := by
  have h := mul_le_mul_of_nonneg_left
    (componentTerm_norm_bound gs X C R a s x y d e hC hR ha hx hy hsR l)
    (by positivity : 0 ≤ (l+1 : ℝ)^k)
  convert h using 1
  rw [pow_add]
  ring

theorem normTail_nonnegative (gs : ℝ → List Layer) (X : ℝ → ℝ) (C R x y : ℝ)
    (k : ℕ) (d e : Bool) : 0 ≤ normTail gs X C k R d e x y :=
  tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))

theorem weighted_component_summable (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R a s x y : ℝ) (k : ℕ) (d e : Bool) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (ha : 0 < a) (hx : x ∈ Icc a s) (hy : y ∈ Icc a s) (ht : Real.exp 1*s ≤ R)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hp : ∀ g ∈ gs R, g.q ≤ q) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*‖componentTerm gs X (2*q) R d e x y l‖) := by
  have hs : 0 < s := ha.trans_le (hx.1.trans hx.2)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsR : s ≤ R := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (weighted_component_bound gs X (2*q) R a s x y k d e (by linarith) hRp ha hx hy hsR)
    ((RadialStackHighTail.actual_tail_summable gs X q s R (k+2) hq hs hR ht hc hX hp).mul_left _)

theorem normTail_le (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R a s x y : ℝ) (k : ℕ) (d e : Bool) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (ha : 0 < a) (hx : x ∈ Icc a s) (hy : y ∈ Icc a s) (ht : Real.exp 1*s ≤ R)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hp : ∀ g ∈ gs R, g.q ≤ q) :
    normTail gs X (2*q) k R d e x y ≤ gapConstant a^2*weightedTail gs X (2*q) s (k+2) R := by
  have hs : 0 < s := ha.trans_le (hx.1.trans hx.2)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hsR : s ≤ R := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  rw [normTail,weightedTail,← tsum_mul_left]
  exact (weighted_component_summable gs X q R a s x y k d e hq hR ha hx hy ht hc hX hp).tsum_le_tsum
    (weighted_component_bound gs X (2*q) R a s x y k d e (by linarith) hRp ha hx hy hsR)
    ((RadialStackHighTail.actual_tail_summable gs X q s R (k+2) hq hs hR ht hc hX hp).mul_left _)

theorem uniform_normTail_decay (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q a s : ℝ) (k N : ℕ) (hq : 1 ≤ q) (ha : 0 < a) (has : a ≤ s)
    (hc : ∀ R, 1 ≤ R → Chain (gs R) (X R) R)
    (hX : ∀ R, 1 ≤ R → X R ≤ 2*R)
    (hp : ∀ R, 1 ≤ R → ∀ g ∈ gs R, g.q ≤ q)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ d e : Bool, ∀ x ∈ Icc a s, ∀ y ∈ Icc a s,
      R^N*normTail gs X (2*q) k R d e x y < ε := by
  have hlim := (RadialStackHighTail.actual_tail_decay gs X q s (k+2) N hq
    (ha.trans_le has) hc hX hp).mul_const (gapConstant a^2)
  simp only [zero_mul] at hlim
  have hevent := (tendsto_order.1 hlim).2 ε hε
  filter_upwards [hevent,eventually_ge_atTop (1 : ℝ),eventually_ge_atTop (Real.exp 1*s)] with R hE hR ht
  intro d e x hx y hy
  have h := mul_le_mul_of_nonneg_left
    (normTail_le gs X q R a s x y k d e hq hR ha hx hy ht (hc R hR) (hX R hR) (hp R hR))
    (pow_nonneg (zero_lt_one.trans_le hR).le N)
  apply lt_of_le_of_lt h
  convert hE using 1
  ring

end OQ14.RadialReactionTail

#print axioms OQ14.RadialReactionTail.componentTerm_norm_bound
#print axioms OQ14.RadialReactionTail.weighted_component_bound
#print axioms OQ14.RadialReactionTail.normTail_nonnegative
#print axioms OQ14.RadialReactionTail.weighted_component_summable
#print axioms OQ14.RadialReactionTail.normTail_le
#print axioms OQ14.RadialReactionTail.uniform_normTail_decay

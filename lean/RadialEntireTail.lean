import RadialEntireReaction

/-! All-order absolute high-degree scalar reaction tails, including the analytic origin. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialEntireTail

open Filter Set OQ14.RadialStack OQ14.RadialHighOrderTail OQ14.RadialEntireReaction
open scoped Topology

def term (gs : ℝ → List Layer) (X : ℝ → ℝ) (q R : ℝ)
    (m n : ℕ) (z w : ℂ) (l : ℕ) : ℂ :=
  if hR : 0 < R then
    if 2*q*R ≤ l then component l m n (gs R) R (X R) hR z w else 0
  else 0

def normTail (gs : ℝ → List Layer) (X : ℝ → ℝ) (q : ℝ) (k : ℕ)
    (R : ℝ) (m n : ℕ) (z w : ℂ) : ℝ :=
  ∑' l : ℕ, (l+1 : ℝ)^k*‖term gs X q R m n z w l‖

theorem term_norm_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R b : ℝ) (m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hR : 0 < R)
    (hb : 0 < b) (hbR : b ≤ R) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (l : ℕ) : ‖term gs X q R m n z w l‖ ≤
      Real.exp (2*b^2)*reactionTerm gs X (2*q) b R l := by
  rw [term,reactionTerm,dif_pos hR,dif_pos hR]
  split_ifs with hl
  · have hh := RadialStackHighTail.cutoff_covers_high_range q R hq hR.le l hl
    have hs : b^2 ≤ R^2 := (sq_le_sq₀ hb.le hR.le).mpr hbR
    exact component_norm_bound l m n (gs R) R (X R) b hR hb
      (hs.trans_lt (RadialHighOrderBound.high_order_barrier l R hR hh)) z w hz hw
  · simp

theorem normTail_nonnegative (gs : ℝ → List Layer) (X : ℝ → ℝ) (q R : ℝ)
    (k m n : ℕ) (z w : ℂ) : 0 ≤ normTail gs X q k R m n z w :=
  tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))

theorem weighted_term_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R b : ℝ) (k m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hR : 0 < R)
    (hb : 0 < b) (hbR : b ≤ R) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (l : ℕ) : (l+1 : ℝ)^k*‖term gs X q R m n z w l‖ ≤
      Real.exp (2*b^2)*((l+1 : ℝ)^k*reactionTerm gs X (2*q) b R l) := by
  have h := mul_le_mul_of_nonneg_left (term_norm_bound gs X q R b m n z w hq hR hb hbR hz hw l)
    (by positivity : 0 ≤ (l+1 : ℝ)^k)
  convert h using 1
  ring

theorem weighted_norm_summable (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R b : ℝ) (k m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hp : ∀ g ∈ gs R, g.q ≤ q) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*‖term gs X q R m n z w l‖) := by
  have hbR : b ≤ R := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (weighted_term_bound gs X q R b k m n z w hq (zero_lt_one.trans_le hR) hb hbR hz hw)
    ((RadialStackHighTail.actual_tail_summable gs X q b R k hq hb hR ht hc hX hp).mul_left _)

theorem normTail_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R b : ℝ) (k m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hp : ∀ g ∈ gs R, g.q ≤ q) :
    normTail gs X q k R m n z w ≤ Real.exp (2*b^2)*weightedTail gs X (2*q) b k R := by
  have hbR : b ≤ R := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  rw [normTail,weightedTail,← tsum_mul_left]
  exact (weighted_norm_summable gs X q R b k m n z w hq hR hb ht hz hw hc hX hp).tsum_le_tsum
    (weighted_term_bound gs X q R b k m n z w hq (zero_lt_one.trans_le hR) hb hbR hz hw)
    ((RadialStackHighTail.actual_tail_summable gs X q b R k hq hb hR ht hc hX hp).mul_left _)

theorem complex_series_summable (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q R b : ℝ) (k m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hp : ∀ g ∈ gs R, g.q ≤ q) :
    Summable (fun l : ℕ => ((l+1 : ℝ)^k) • term gs X q R m n z w l) := by
  apply Summable.of_norm_bounded _ (weighted_norm_summable gs X q R b k m n z w hq hR hb ht hz hw hc hX hp)
  intro l
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (l+1 : ℝ)^k),le_refl]

theorem uniform_normTail_decay (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q s b : ℝ) (k m n N : ℕ) (hq : 1 ≤ q) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hc : ∀ R, 1 ≤ R → Chain (gs R) (X R) R)
    (hX : ∀ R, 1 ≤ R → X R ≤ 2*R) (hp : ∀ R, 1 ≤ R → ∀ g ∈ gs R, g.q ≤ q)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ s → ∀ w : ℂ, ‖w‖ ≤ s →
      R^N*normTail gs X q k R m n z w < ε := by
  have hlim := (RadialStackHighTail.actual_tail_decay gs X q b k N hq hb hc hX hp).mul_const (Real.exp (2*b^2))
  simp only [zero_mul] at hlim
  have hevent := (tendsto_order.1 hlim).2 ε hε
  filter_upwards [hevent,eventually_ge_atTop (1 : ℝ),eventually_ge_atTop (Real.exp 1*b)] with R hE hR ht
  intro z hz w hw
  have h := mul_le_mul_of_nonneg_left
    (normTail_bound gs X q R b k m n z w hq hR hb ht (by linarith) (by linarith)
      (hc R hR) (hX R hR) (hp R hR))
    (pow_nonneg (zero_lt_one.trans_le hR).le N)
  apply lt_of_le_of_lt h
  convert hE using 1
  ring

end OQ14.RadialEntireTail

#print axioms OQ14.RadialEntireTail.term_norm_bound
#print axioms OQ14.RadialEntireTail.normTail_nonnegative
#print axioms OQ14.RadialEntireTail.weighted_term_bound
#print axioms OQ14.RadialEntireTail.weighted_norm_summable
#print axioms OQ14.RadialEntireTail.normTail_bound
#print axioms OQ14.RadialEntireTail.complex_series_summable
#print axioms OQ14.RadialEntireTail.uniform_normTail_decay

import RadialHighOrderTail

/-! Actual finite-stack geometry supplies the high-order reaction barrier. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialStackHighTail

open Filter OQ14.RadialStack OQ14.RadialHighOrderTail OQ14.HankelRealBasis
open scoped Topology

theorem chain_layer_outer_le {gs : List Layer} {X R : ℝ} (h : Chain gs X R) :
    ∀ g ∈ gs, g.b ≤ X := by
  induction h with
  | nil R => simp
  | cons g gs R h ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (ih a ha).trans g.ordered

theorem common_stack_barrier (l : ℕ) {gs : List Layer} {X R : ℝ}
    (h : Chain gs X R) (q : ℝ) (hq : 1 ≤ q) (_hR : 0 < R)
    (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs, g.q ≤ q) (hl : 2*q*R ≤ l) :
    ∀ g ∈ gs, g.q^2*g.b^2 ≤ HankelEnergy.angular l := by
  intro g hg
  have hb : 0 < g.b := g.a_pos.trans_le g.ordered
  have hgb : g.b ≤ 2*R := (chain_layer_outer_le h g hg).trans hX
  have hprod : g.q*g.b ≤ (l : ℝ) := by
    calc
      _ ≤ q*(2*R) := mul_le_mul (hparams g hg) hgb hb.le (by linarith)
      _ ≤ l := by nlinarith [hl]
  have hsq := (sq_le_sq₀ (mul_pos g.q_pos hb).le (Nat.cast_nonneg l)).mpr hprod
  unfold HankelEnergy.angular
  nlinarith [Nat.cast_nonneg (α := ℝ) l]

theorem cutoff_covers_high_range (q R : ℝ) (hq : 1 ≤ q) (hR : 0 ≤ R) (l : ℕ)
    (hl : 2*q*R ≤ l) : 2*R ≤ l := by
  nlinarith

theorem cutoff_windows_cover (q R : ℝ) (l : ℕ) :
    (l : ℝ) ≤ 2*q*R ∨ 2*q*R ≤ l := le_total _ _

theorem actual_reaction_bound (l : ℕ) {gs : List Layer} {R X : ℝ}
    (h : Chain gs X R) (q s : ℝ) (hq : 1 ≤ q) (hR : 0 < R)
    (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs, g.q ≤ q)
    (hs : 0 < s) (hsR : s ≤ R) (hl : 2*q*R ≤ l) :
    ‖RadialSource.gamma l gs R X hR‖*(regular l s)^2 ≤
      4*Real.exp (3*R/2)*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1)) :=
  RadialHighOrderBound.actual_reaction_high_order l gs R X s hR
    (hR.trans_le (chain_ordered h)) hs hsR (cutoff_covers_high_range q R hq hR.le l hl)
    (common_stack_barrier l h q hq hR hX hparams hl)

theorem actual_tail_summable (gs : ℝ → List Layer) (X : ℝ → ℝ) (q s R : ℝ) (k : ℕ)
    (hq : 1 ≤ q) (hs : 0 < s) (hR : 1 ≤ R) (ht : Real.exp 1*s ≤ R)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R)
    (hparams : ∀ g ∈ gs R, g.q ≤ q) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*reactionTerm gs X (2*q) s R l) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  exact weighted_reaction_summable gs X (2*q) s R k (by linarith) hs hR ht
    (hRp.trans_le (chain_ordered hc))
    (fun l hl => common_stack_barrier l hc q hq hRp hX hparams hl)

theorem actual_tail_bound (gs : ℝ → List Layer) (X : ℝ → ℝ) (q s R : ℝ) (k : ℕ)
    (hq : 1 ≤ q) (hs : 0 < s) (hR : 1 ≤ R) (ht : Real.exp 1*s ≤ R)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R)
    (hparams : ∀ g ∈ gs R, g.q ≤ q) :
    weightedTail gs X (2*q) s k R ≤ 4*s^2*Real.exp (-R/2)*geometricWeight k := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  exact weightedTail_le gs X (2*q) s R k (by linarith) hs hR ht
    (hRp.trans_le (chain_ordered hc))
    (fun l hl => common_stack_barrier l hc q hq hRp hX hparams hl)

theorem actual_tail_decay (gs : ℝ → List Layer) (X : ℝ → ℝ) (q s : ℝ) (k N : ℕ)
    (hq : 1 ≤ q) (hs : 0 < s)
    (hc : ∀ R, 1 ≤ R → Chain (gs R) (X R) R)
    (hX : ∀ R, 1 ≤ R → X R ≤ 2*R)
    (hparams : ∀ R, 1 ≤ R → ∀ g ∈ gs R, g.q ≤ q) :
    Tendsto (fun R : ℝ => R^N*weightedTail gs X (2*q) s k R) atTop (𝓝 0) := by
  apply weightedTail_decay gs X (2*q) s k N (by linarith) hs
  · intro R hR
    exact (zero_lt_one.trans_le hR).trans_le (chain_ordered (hc R hR))
  · intro R hR l hl
    exact common_stack_barrier l (hc R hR) q hq (zero_lt_one.trans_le hR)
      (hX R hR) (hparams R hR) hl

theorem actual_tail_tendsto_zero (gs : ℝ → List Layer) (X : ℝ → ℝ) (q s : ℝ) (k : ℕ)
    (hq : 1 ≤ q) (hs : 0 < s)
    (hc : ∀ R, 1 ≤ R → Chain (gs R) (X R) R)
    (hX : ∀ R, 1 ≤ R → X R ≤ 2*R)
    (hparams : ∀ R, 1 ≤ R → ∀ g ∈ gs R, g.q ≤ q) :
    Tendsto (weightedTail gs X (2*q) s k) atTop (𝓝 0) := by
  simpa only [pow_zero,one_mul] using actual_tail_decay gs X q s k 0 hq hs hc hX hparams

end OQ14.RadialStackHighTail

#print axioms OQ14.RadialStackHighTail.chain_layer_outer_le
#print axioms OQ14.RadialStackHighTail.common_stack_barrier
#print axioms OQ14.RadialStackHighTail.cutoff_covers_high_range
#print axioms OQ14.RadialStackHighTail.cutoff_windows_cover
#print axioms OQ14.RadialStackHighTail.actual_reaction_bound
#print axioms OQ14.RadialStackHighTail.actual_tail_summable
#print axioms OQ14.RadialStackHighTail.actual_tail_bound
#print axioms OQ14.RadialStackHighTail.actual_tail_decay
#print axioms OQ14.RadialStackHighTail.actual_tail_tendsto_zero

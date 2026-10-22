import RadialMiddleTail

/-! Actual low-range scalar reaction bounds and uniform angular tail control. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialLowTail

open Filter OQ14.RadialStack OQ14.RadialEntireReaction OQ14.RiccatiSeriesCoefficients
open OQ14.RiccatiFactorialTail
open scoped Topology

def bound (M d : ℝ) : ℝ := (4/(1-(1/2 : ℝ)^2))^2*Real.exp ((2*M+(1/2 : ℝ)^2)*d)
def prefactor (M d b : ℝ) : ℝ := bound M d*Real.exp (b^2)

theorem actual_gamma_low_bound (l : ℕ) {gs : List Layer} {X R : ℝ}
    (hc : Chain gs X R) (M d : ℝ) (hM : 0 ≤ M) (hR : 0 < R)
    (hd : X-R ≤ d) (hl : 2*((l : ℝ)+1) ≤ R)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    ‖RadialSource.gamma l gs R X hR‖ ≤ bound M d := by
  have h := RadialSource.gamma_low_range l hc M (1/2) hR (by norm_num)
    (RadialMiddleTail.low_degree_barrier l R hR.le hl) hp
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hd (by positivity))) (sq_nonneg _)

def term (gs : ℝ → List Layer) (X : ℝ → ℝ) (R : ℝ)
    (m n : ℕ) (z w : ℂ) (l : ℕ) : ℂ :=
  if hR : 0 < R then
    if 2*((l : ℝ)+1) ≤ R then component l m n (gs R) R (X R) hR z w else 0
  else 0

def majorant (b : ℝ) (k l : ℕ) : ℝ := (l+1 : ℝ)^k*(amplitude l 0*b^(l+1))^2

theorem majorant_summable (b : ℝ) (k : ℕ) (hb : 0 ≤ b) : Summable (majorant b k) := by
  simpa only [majorant,zero_mul,Real.exp_zero,mul_one] using weighted_amplitudes_summable k b 0 hb

theorem majorant_nonnegative (b : ℝ) (k l : ℕ) : 0 ≤ majorant b k l := by
  dsimp [majorant]
  positivity

theorem term_norm_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (M d R b : ℝ) (m n : ℕ) (z w : ℂ) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (l : ℕ) :
    ‖term gs X R m n z w l‖ ≤ prefactor M d b*(amplitude l 0*b^(l+1))^2 := by
  rw [term,dif_pos hR]
  split_ifs with hl
  · have hgamma := actual_gamma_low_bound l hc M d hM hR hd hl hp
    have hcomp := RadialMiddleTail.component_amplitude_bound l m n (gs R) R (X R) b hR hb z w hz hw
    apply hcomp.trans
    have hm := mul_le_mul_of_nonneg_right hgamma
      (by positivity : 0 ≤ Real.exp (b^2)*(amplitude l 0*b^(l+1))^2)
    dsimp [prefactor]
    convert hm using 1 <;> ring
  · simp only [norm_zero]
    dsimp [prefactor,bound]
    positivity

theorem weighted_term_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (M d R b : ℝ) (k m n : ℕ) (z w : ℂ) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (l : ℕ) :
    (l+1 : ℝ)^k*‖term gs X R m n z w l‖ ≤ prefactor M d b*majorant b k l := by
  have h := mul_le_mul_of_nonneg_left (term_norm_bound gs X M d R b m n z w hM hR hb hz hw hc hd hp l)
    (by positivity : 0 ≤ (l+1 : ℝ)^k)
  dsimp [majorant]
  convert h using 1
  ring

theorem weighted_norm_summable (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (M d R b : ℝ) (k m n : ℕ) (z w : ℂ) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*‖term gs X R m n z w l‖) := by
  exact Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (weighted_term_bound gs X M d R b k m n z w hM hR hb hz hw hc hd hp)
    ((majorant_summable b k hb).mul_left _)

def angularTail (gs : ℝ → List Layer) (X : ℝ → ℝ) (k m n : ℕ)
    (T R : ℝ) (z w : ℂ) : ℝ :=
  ∑' l : ℕ, if T ≤ 4*(l : ℝ) then (l+1 : ℝ)^k*‖term gs X R m n z w l‖ else 0

theorem angularTail_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (M d T R b : ℝ) (k m n : ℕ) (z w : ℂ) (hM : 0 ≤ M) (hR : 0 < R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    angularTail gs X k m n T R z w ≤ prefactor M d b*movingTail (majorant b k) T := by
  have hleft : Summable (fun l : ℕ => if T ≤ 4*(l : ℝ) then (l+1 : ℝ)^k*‖term gs X R m n z w l‖ else 0) := by
    apply Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_)
      (weighted_norm_summable gs X M d R b k m n z w hM hR hb hz hw hc hd hp)
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  have hright : Summable (fun l : ℕ => if T ≤ 4*(l : ℝ) then majorant b k l else 0) := by
    apply Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) (majorant_summable b k hb)
    · split_ifs
      · exact majorant_nonnegative b k l
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact majorant_nonnegative b k l
  rw [angularTail,movingTail,← tsum_mul_left]
  apply hleft.tsum_le_tsum _ (hright.mul_left _)
  intro l
  split_ifs
  · exact weighted_term_bound gs X M d R b k m n z w hM hR hb hz hw hc hd hp l
  · simp

theorem uniform_angularTail_decay (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (M d s b : ℝ) (k m n : ℕ) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hc : ∀ R, 1 ≤ R → Chain (gs R) (X R) R) (hd : ∀ R, 1 ≤ R → X R-R ≤ d)
    (hp : ∀ R, 1 ≤ R → ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ ≤ s → ∀ w : ℂ, ‖w‖ ≤ s →
      angularTail gs X k m n T R z w < ε := by
  have hlim := (movingTail_tendsto_zero (majorant b k) (majorant_summable b k hb)).const_mul (prefactor M d b)
  simp only [mul_zero] at hlim
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with T hT
  intro R hR z hz w hw
  exact (angularTail_bound gs X M d T R b k m n z w hM (zero_lt_one.trans_le hR) hb
    (by linarith) (by linarith) (hc R hR) (hd R hR) (hp R hR)).trans_lt hT

end OQ14.RadialLowTail

#print axioms OQ14.RadialLowTail.actual_gamma_low_bound
#print axioms OQ14.RadialLowTail.majorant_summable
#print axioms OQ14.RadialLowTail.majorant_nonnegative
#print axioms OQ14.RadialLowTail.term_norm_bound
#print axioms OQ14.RadialLowTail.weighted_term_bound
#print axioms OQ14.RadialLowTail.weighted_norm_summable
#print axioms OQ14.RadialLowTail.angularTail_bound
#print axioms OQ14.RadialLowTail.uniform_angularTail_decay

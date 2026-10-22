import RadialIntermediateBound
import RadialEntireReaction
import RiccatiFactorialTail

/-! Actual intermediate reaction terms have a fixed factorial degree majorant. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialMiddleTail

open Filter OQ14.RadialStack OQ14.RadialEntireReaction OQ14.RiccatiOriginSeries
open OQ14.RiccatiCompactDerivatives OQ14.RiccatiSeriesCoefficients OQ14.RadialIntermediateBound
open OQ14.RiccatiFactorialTail
open scoped Topology

def degreeRate (q : ℝ) : ℝ := 16*HankelIntermediateBounds.exponent q
def prefactor (q M d b : ℝ) : ℝ :=
  (frameConstant q)^2*Real.exp ((2*M+angularBound q)*d+b^2)

theorem exponent_nonnegative (q : ℝ) (hq : 1 ≤ q) : 0 ≤ HankelIntermediateBounds.exponent q := by
  have hlog : 0 ≤ Real.log (4*q) := Real.log_nonneg (by linarith)
  dsimp [HankelIntermediateBounds.exponent]
  positivity

theorem outside_low_degree (l : ℕ) (R : ℝ) (hR : 4 ≤ R)
    (hl : ¬ 2*((l : ℝ)+1) ≤ R) : R ≤ 4*(l : ℝ) := by
  push_neg at hl
  linarith

theorem low_degree_barrier (l : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hl : 2*((l : ℝ)+1) ≤ R) : HankelEnergy.angular l ≤ (1/2 : ℝ)^2*R^2 := by
  have hn : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hsq : (2*((l : ℝ)+1))^2 ≤ R^2 := (sq_le_sq₀ (by positivity) hR).mpr hl
  dsimp [HankelEnergy.angular]
  nlinarith

theorem component_amplitude_bound (l m n : ℕ) (gs : List Layer) (R X b : ℝ)
    (hR : 0 < R) (hb : 0 ≤ b) (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    ‖component l m n gs R X hR z w‖ ≤
      ‖RadialSource.gamma l gs R X hR‖*Real.exp (b^2)*(amplitude l 0*b^(l+1))^2 := by
  have h1 := origin_iteratedDeriv_bound l m b hb z hz
  have h2 := origin_iteratedDeriv_bound l n b hb w hw
  have hbase : 0 ≤ amplitude l 0*b^(l+1)*Real.exp (b^2/2) := by
    exact mul_nonneg (mul_nonneg (amplitude_pos l 0).le (pow_nonneg hb _)) (Real.exp_pos _).le
  have hp := mul_le_mul h1 h2 (norm_nonneg _) hbase
  have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (RadialSource.gamma l gs R X hR))
  simp only [component,norm_mul]
  convert hm using 1
  · ring
  · rw [show b^2=b^2/2+b^2/2 by ring,Real.exp_add]
    ring

def term (gs : ℝ → List Layer) (X : ℝ → ℝ) (q R : ℝ)
    (m n : ℕ) (z w : ℂ) (l : ℕ) : ℂ :=
  if hR : 0 < R then
    if ¬ 2*((l : ℝ)+1) ≤ R ∧ (l : ℝ) ≤ 2*q*R then
      component l m n (gs R) R (X R) hR z w else 0
  else 0

def normTail (gs : ℝ → List Layer) (X : ℝ → ℝ) (q : ℝ) (k : ℕ)
    (R : ℝ) (m n : ℕ) (z w : ℂ) : ℝ := ∑' l : ℕ, (l+1 : ℝ)^k*‖term gs X q R m n z w l‖

theorem term_degree_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q M d R b : ℝ) (m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (l : ℕ) :
    ‖term gs X q R m n z w l‖ ≤ prefactor q M d b *
      (if R ≤ 4*(l : ℝ) then Real.exp (degreeRate q*(l : ℝ))*(amplitude l 0*b^(l+1))^2 else 0) := by
  have hRp : 0 < R := by linarith
  rw [term,dif_pos hRp]
  split_ifs with hl hlower hlower
  · have hgamma := actual_gamma_window_bound l hc q M d hq hM (by linarith) hX hd hl.2 hp
    have hcomp := component_amplitude_bound l m n (gs R) R (X R) b hRp hb z w hz hw
    have hexp : Real.exp (4*HankelIntermediateBounds.exponent q*R) ≤ Real.exp (degreeRate q*(l : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hlower (exponent_nonnegative q hq)
      dsimp [degreeRate]
      nlinarith
    apply hcomp.trans
    have hgamma' : ‖RadialSource.gamma l (gs R) R (X R) hRp‖ ≤
        (frameConstant q)^2*Real.exp ((2*M+angularBound q)*d)*Real.exp (degreeRate q*(l : ℝ)) := by
      apply hgamma.trans
      rw [Real.exp_add]
      have hm := mul_le_mul_of_nonneg_left hexp
        (by positivity : 0 ≤ (frameConstant q)^2*Real.exp ((2*M+angularBound q)*d))
      convert hm using 1
      ring
    have hm := mul_le_mul_of_nonneg_right hgamma'
      (by positivity : 0 ≤ Real.exp (b^2)*(amplitude l 0*b^(l+1))^2)
    convert hm using 1
    · ring
    · dsimp [prefactor]
      rw [Real.exp_add]
      ring
  · exact (hlower (outside_low_degree l R hR hl.1)).elim
  · simp only [norm_zero]
    dsimp [prefactor]
    positivity
  · simp

def majorant (q b : ℝ) (k : ℕ) (l : ℕ) : ℝ :=
  (l+1 : ℝ)^k*Real.exp (degreeRate q*(l : ℝ))*(amplitude l 0*b^(l+1))^2

theorem majorant_summable (q b : ℝ) (k : ℕ) (hb : 0 ≤ b) : Summable (majorant q b k) :=
  weighted_amplitudes_summable k b (degreeRate q) hb

theorem majorant_nonnegative (q b : ℝ) (k l : ℕ) : 0 ≤ majorant q b k l := by
  dsimp [majorant]
  positivity

theorem weighted_term_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q M d R b : ℝ) (k N m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (l : ℕ) :
    R^N*((l+1 : ℝ)^k*‖term gs X q R m n z w l‖) ≤
      4^N*prefactor q M d b*(if R ≤ 4*(l : ℝ) then majorant q b (k+N) l else 0) := by
  have hterm := term_degree_bound gs X q M d R b m n z w hq hM hR hb hz hw hc hX hd hp l
  by_cases hl : R ≤ 4*(l : ℝ)
  · rw [if_pos hl] at hterm ⊢
    have hpow : R^N ≤ 4^N*(l+1 : ℝ)^N := by
      have h := pow_le_pow_left₀ (by linarith : 0 ≤ R) (by linarith : R ≤ 4*(l+1 : ℝ)) N
      simpa only [mul_pow] using h
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (l+1 : ℝ)^k))
      hterm (norm_nonneg _) (by positivity)
    convert h using 1
    · ring
    · dsimp [majorant]
      rw [pow_add]
      ring
  · rw [if_neg hl] at hterm ⊢
    have h := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ R^N*(l+1 : ℝ)^k)
    simpa only [mul_zero,mul_assoc] using h

theorem weighted_norm_summable (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q M d R b : ℝ) (k m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*‖term gs X q R m n z w l‖) := by
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun l => ?_) ((majorant_summable q b k hb).mul_left (prefactor q M d b))
  have h := weighted_term_bound gs X q M d R b k 0 m n z w hq hM hR hb hz hw hc hX hd hp l
  simp only [pow_zero,one_mul,Nat.add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by dsimp [prefactor]; positivity)
  split_ifs
  · exact le_rfl
  · exact majorant_nonnegative q b k l

theorem normTail_power_bound (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q M d R b : ℝ) (k N m n : ℕ) (z w : ℂ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hb : 0 ≤ b) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b)
    (hc : Chain (gs R) (X R) R) (hX : X R ≤ 2*R) (hd : X R-R ≤ d)
    (hp : ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    R^N*normTail gs X q k R m n z w ≤
      4^N*prefactor q M d b*movingTail (majorant q b (k+N)) R := by
  have hmask : Summable (fun l : ℕ => if R ≤ 4*(l : ℝ) then majorant q b (k+N) l else 0) := by
    apply Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_) (majorant_summable q b (k+N) hb)
    · split_ifs
      · exact majorant_nonnegative q b (k+N) l
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact majorant_nonnegative q b (k+N) l
  rw [normTail,movingTail,← tsum_mul_left,← tsum_mul_left]
  exact ((weighted_norm_summable gs X q M d R b k m n z w hq hM hR hb hz hw hc hX hd hp).mul_left _).tsum_le_tsum
    (weighted_term_bound gs X q M d R b k N m n z w hq hM hR hb hz hw hc hX hd hp)
    (hmask.mul_left _)

theorem uniform_normTail_decay (gs : ℝ → List Layer) (X : ℝ → ℝ)
    (q M d s b : ℝ) (k N m n : ℕ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hc : ∀ R, 4 ≤ R → Chain (gs R) (X R) R)
    (hX : ∀ R, 4 ≤ R → X R ≤ 2*R) (hd : ∀ R, 4 ≤ R → X R-R ≤ d)
    (hp : ∀ R, 4 ≤ R → ∀ g ∈ gs R, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ s → ∀ w : ℂ, ‖w‖ ≤ s →
      R^N*normTail gs X q k R m n z w < ε := by
  have hlim := (movingTail_tendsto_zero (majorant q b (k+N))
    (majorant_summable q b (k+N) hb)).const_mul (4^N*prefactor q M d b)
  simp only [mul_zero] at hlim
  have hevent := (tendsto_order.1 hlim).2 ε hε
  filter_upwards [hevent,eventually_ge_atTop (4 : ℝ)] with R hE hR
  intro z hz w hw
  exact (normTail_power_bound gs X q M d R b k N m n z w hq hM hR hb
    (by linarith) (by linarith) (hc R hR) (hX R hR) (hd R hR) (hp R hR)).trans_lt hE

end OQ14.RadialMiddleTail

#print axioms OQ14.RadialMiddleTail.exponent_nonnegative
#print axioms OQ14.RadialMiddleTail.outside_low_degree
#print axioms OQ14.RadialMiddleTail.low_degree_barrier
#print axioms OQ14.RadialMiddleTail.component_amplitude_bound
#print axioms OQ14.RadialMiddleTail.term_degree_bound
#print axioms OQ14.RadialMiddleTail.majorant_summable
#print axioms OQ14.RadialMiddleTail.majorant_nonnegative
#print axioms OQ14.RadialMiddleTail.weighted_term_bound
#print axioms OQ14.RadialMiddleTail.weighted_norm_summable
#print axioms OQ14.RadialMiddleTail.normTail_power_bound
#print axioms OQ14.RadialMiddleTail.uniform_normTail_decay

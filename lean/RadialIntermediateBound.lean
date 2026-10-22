import RadialStackHighTail
import HankelIntermediateBounds

/-! Actual exponential transfer/source bounds throughout the complementary degree window. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialIntermediateBound

open OQ14.HankelCoefficientBounds OQ14.HankelRealBasis OQ14.RadialStack

def frameConstant (q : ℝ) : ℝ := 1+(1+2*q)^2
def angularBound (q : ℝ) : ℝ := 4*q^2+2*q

theorem frobenius_window_bound (l : ℕ) (q R x : ℝ) (hq : 1 ≤ q) (hR : 0 < R)
    (hRx : R ≤ x) (hxR : x ≤ 2*R) (hl : (l : ℝ) ≤ 2*q*R) :
    frobeniusSq l x ≤ frameConstant q*Real.exp (2*HankelIntermediateBounds.exponent q*R) := by
  have h1 := HankelIntermediateBounds.xi_intermediate_bound l q R x hq hR hRx hxR hl
  have h2 := HankelIntermediateBounds.xiD_intermediate_bound l q R x hq hR hRx hxR hl
  rw [frobeniusSq_eq,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
  have hh1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hh2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  apply (add_le_add hh1 hh2).trans_eq
  rw [show 2*HankelIntermediateBounds.exponent q*R=HankelIntermediateBounds.exponent q*R+HankelIntermediateBounds.exponent q*R by ring,Real.exp_add]
  dsimp [frameConstant]
  ring

theorem window_angular_bound (l : ℕ) (q R : ℝ) (hq : 1 ≤ q) (hR : 1 ≤ R)
    (hl : (l : ℝ) ≤ 2*q*R) : HankelEnergy.angular l ≤ angularBound q*R^2 := by
  have hn : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hsq : (l : ℝ)^2 ≤ (2*q*R)^2 :=
    (sq_le_sq₀ hn (by positivity)).mpr hl
  have hlin : (l : ℝ) ≤ 2*q*R^2 := by
    have hRR : R ≤ R^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hRR (by linarith : 0 ≤ 2*q)
    exact hl.trans hmul
  dsimp [HankelEnergy.angular,angularBound]
  nlinarith

theorem actual_gamma_window_bound (l : ℕ) {gs : List Layer} {X R : ℝ}
    (hc : Chain gs X R) (q M d : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d) (hl : (l : ℝ) ≤ 2*q*R)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    ‖RadialSource.gamma l gs R X (zero_lt_one.trans_le hR)‖ ≤
      (frameConstant q)^2*Real.exp (4*HankelIntermediateBounds.exponent q*R+(2*M+angularBound q)*d) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hRX : R ≤ X := chain_ordered hc
  have hXp : 0 < X := hRp.trans_le hRX
  have hA : 0 ≤ angularBound q := by dsimp [angularBound]; positivity
  have hν := window_angular_bound l q R hq hR hl
  have hcost := chain_cost_bound l hc M (angularBound q) hRp hA hν hp
  have hcost' : totalCost l gs ≤ (2*M+angularBound q)*d :=
    hcost.trans (mul_le_mul_of_nonneg_left hd (by positivity))
  have hF0 : 0 ≤ frobeniusSq l R := by unfold frobeniusSq; positivity
  have hF1 : 0 ≤ frobeniusSq l X := by unfold frobeniusSq; positivity
  have hC : 0 ≤ frameConstant q := by dsimp [frameConstant]; positivity
  have h1 := frobenius_window_bound l q R R hq hRp le_rfl (by linarith) hl
  have h2 := frobenius_window_bound l q R X hq hRp hRX hX hl
  have he := Real.exp_le_exp.mpr hcost'
  apply (RadialSource.gamma_stack_bound l gs R X hRp hXp).trans
  have hm := mul_le_mul (mul_le_mul h1 he (Real.exp_pos _).le (by positivity)) h2 hF1 (by positivity)
  apply hm.trans_eq
  calc
    _ = (frameConstant q)^2*(Real.exp (2*HankelIntermediateBounds.exponent q*R)*
        Real.exp (2*HankelIntermediateBounds.exponent q*R)*Real.exp ((2*M+angularBound q)*d)) := by ring
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 2
      ring

end OQ14.RadialIntermediateBound

#print axioms OQ14.RadialIntermediateBound.frobenius_window_bound
#print axioms OQ14.RadialIntermediateBound.window_angular_bound
#print axioms OQ14.RadialIntermediateBound.actual_gamma_window_bound

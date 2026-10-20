import RiccatiSeriesCoefficients
import RiccatiRaising
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # The genuine entire origin series for the regular Riccati function -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.RiccatiOriginSeries

open Complex Filter Set Metric OQ14.RiccatiSeriesCoefficients OQ14.RiccatiRaising OQ14.ModalAlgebra
open scoped Topology

def term (l m : ℕ) (z : ℂ) : ℂ := (coeff l m : ℂ)*z^(l+1+2*m)
def termD (l m : ℕ) (z : ℂ) : ℂ := (coeff l m : ℂ)*(l+1+2*m : ℕ)*z^(l+2*m)
def origin (l : ℕ) (z : ℂ) : ℂ := ∑' m, term l m z
def originD (l : ℕ) (z : ℂ) : ℂ := ∑' m, termD l m z

theorem term_norm (l m : ℕ) (z : ℂ) :
    ‖term l m z‖ = amplitude l m*‖z‖^(l+1+2*m) := by
  simp only [term,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,coeff_abs]

theorem terms_summable (l : ℕ) (z : ℂ) : Summable (fun m => term l m z) := by
  apply Summable.of_norm_bounded
    (fun m => (amplitude l 0*‖z‖^(l+1))*((‖z‖^2/2)^m/(Nat.factorial m : ℝ)))
    ((Real.summable_pow_div_factorial (‖z‖^2/2)).mul_left _)
  intro m
  rw [term_norm]
  exact power_majorant l m ‖z‖ (norm_nonneg z)

theorem term_hasDerivAt (l m : ℕ) (z : ℂ) : HasDerivAt (term l m) (termD l m z) z := by
  convert (hasDerivAt_pow (l+1+2*m) z).const_mul (coeff l m : ℂ) using 1
  simp only [termD,show l+1+2*m-1=l+2*m by omega,mul_assoc]

theorem termD_norm (l m : ℕ) (z : ℂ) :
    ‖termD l m z‖ = amplitude l m*(l+1+2*m)*‖z‖^(l+2*m) := by
  rw [termD,norm_mul,norm_mul,norm_pow,Complex.norm_natCast]
  rw [Complex.norm_real,Real.norm_eq_abs,coeff_abs]
  push_cast
  rfl

theorem termD_norm_le (l m : ℕ) (b : ℝ) (hb : 1 ≤ b) (z : ℂ) (hz : ‖z‖ ≤ b) :
    ‖termD l m z‖ ≤ (amplitude l 0*(l+2)*b^(l+1))*((b^2)^m/(Nat.factorial m : ℝ)) := by
  rw [termD_norm]
  have hpow : ‖z‖^(l+2*m) ≤ b^(l+1+2*m) :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans (pow_le_pow_right₀ hb (by omega))
  exact (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (amplitude_pos l m).le (by positivity))).trans
    (derivative_power_majorant l m b (zero_le_one.trans hb))

theorem origin_hasDerivAt (l : ℕ) (z : ℂ) : HasDerivAt (origin l) (originD l z) z := by
  let b : ℝ := ‖z‖+1
  have hb : 1 ≤ b := by dsimp [b]; linarith [norm_nonneg z]
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  change HasDerivAt (fun w => ∑' m, term l m w) (∑' m, termD l m z) z
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun m => (amplitude l 0*(l+2)*b^(l+1))*((b^2)^m/(Nat.factorial m : ℝ)))
    ((Real.summable_pow_div_factorial (b^2)).mul_left _)
    isOpen_ball (convex_ball (0 : ℂ) b).isPreconnected
  · intro m w _
    exact term_hasDerivAt l m w
  · intro m w hw
    exact termD_norm_le l m b hb w (mem_ball_zero_iff.mp hw).le
  · exact (mem_ball_self hbpos : (0 : ℂ) ∈ Metric.ball 0 b)
  · exact terms_summable l 0
  · apply mem_ball_zero_iff.mpr
    dsimp [b]
    linarith

theorem originD_summable (l : ℕ) (z : ℂ) : Summable (fun m => termD l m z) := by
  let b : ℝ := ‖z‖+1
  have hb : 1 ≤ b := by dsimp [b]; linarith [norm_nonneg z]
  exact Summable.of_norm_bounded _
    ((Real.summable_pow_div_factorial (b^2)).mul_left (amplitude l 0*(l+2)*b^(l+1)))
    (fun m => termD_norm_le l m b hb z (by dsimp [b]; linarith))

theorem origin_zero (l : ℕ) : origin l 0 = 0 := by
  have hz (m : ℕ) : term l m 0 = 0 := by
    rw [term,zero_pow (by omega : l+1+2*m ≠ 0),mul_zero]
  simp only [origin,hz,tsum_zero]

theorem origin_zero_degree (z : ℂ) : origin 0 z = Complex.sin z := by
  apply HasSum.tsum_eq
  convert Complex.hasSum_sin z using 1
  funext m
  simp only [term,coeff,amplitude_zero_degree,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_natCast,
    Complex.ofReal_inv,Nat.zero_add,one_div,mul_assoc]
  ring

theorem term_raising (l m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (l+1 : ℕ)/z*term l m z-termD l m z = -2*(m : ℂ)*(coeff l m : ℂ)*z^(l+2*m) := by
  unfold term termD
  rw [show l+1+2*m=(l+2*m)+1 by omega,pow_succ]
  push_cast
  field_simp [hz]
  ring

theorem term_raising_succ (l m : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (l+1 : ℕ)/z*term l (m+1) z-termD l (m+1) z = term (l+1) m z := by
  rw [term_raising l (m+1) z hz,term,coeff_raising]
  rw [show l+2*(m+1)=l+1+1+2*m by omega]
  push_cast
  ring

theorem origin_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    origin (l+1) z = (l+1 : ℕ)/z*origin l z-originD l z := by
  let F : ℕ → ℂ := fun m => (l+1 : ℕ)/z*term l m z-termD l m z
  have hsA := (terms_summable l z).mul_left ((l+1 : ℕ)/z : ℂ)
  have hs := hsA.sub (originD_summable l z)
  have heq : (∑' m, F m) = (l+1 : ℕ)/z*origin l z-originD l z := by
    rw [hsA.tsum_sub (originD_summable l z),tsum_mul_left]
    rfl
  rw [← heq,hs.tsum_eq_zero_add]
  change origin (l+1) z = F 0+∑' m, F (m+1)
  have hF0 : F 0 = 0 := by simp only [F,term_raising l 0 z hz,Nat.cast_zero,mul_zero,zero_mul]
  rw [hF0,zero_add]
  exact tsum_congr (fun m => (term_raising_succ l m z hz).symm)

theorem origin_eq_psi (l : ℕ) : ∀ z : ℂ, z ≠ 0 → origin l z = psi l z := by
  induction l with
  | zero => intro z _; rw [origin_zero_degree,psi_zero_degree]
  | succ l ih =>
    intro z hz
    have heq : psi l =ᶠ[𝓝 z] origin l := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      exact (ih w hw).symm
    have hd := ((origin_hasDerivAt l z).congr_of_eventuallyEq heq).unique (psi_hasDerivAt l z hz)
    rw [origin_raising l z hz,psi_raising l z hz,ih z hz,hd]

theorem originD_eq_psiD (l : ℕ) (z : ℂ) (hz : z ≠ 0) : originD l z = psiD l z := by
  have heq : psi l =ᶠ[𝓝 z] origin l := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
    exact (origin_eq_psi l w hw).symm
  exact ((origin_hasDerivAt l z).congr_of_eventuallyEq heq).unique (psi_hasDerivAt l z hz)

theorem psi_hasSum (l : ℕ) (z : ℂ) (hz : z ≠ 0) : HasSum (fun m => term l m z) (psi l z) := by
  rw [← origin_eq_psi l z hz]
  exact (terms_summable l z).hasSum

theorem origin_analyticAt (l : ℕ) (z : ℂ) : AnalyticAt ℂ (origin l) z := by
  have hd : Differentiable ℂ (origin l) := fun w => (origin_hasDerivAt l w).differentiableAt
  exact hd.analyticAt z

end OQ14.RiccatiOriginSeries

#print axioms OQ14.RiccatiOriginSeries.term_norm
#print axioms OQ14.RiccatiOriginSeries.terms_summable
#print axioms OQ14.RiccatiOriginSeries.term_hasDerivAt
#print axioms OQ14.RiccatiOriginSeries.termD_norm
#print axioms OQ14.RiccatiOriginSeries.termD_norm_le
#print axioms OQ14.RiccatiOriginSeries.origin_hasDerivAt
#print axioms OQ14.RiccatiOriginSeries.originD_summable
#print axioms OQ14.RiccatiOriginSeries.origin_zero
#print axioms OQ14.RiccatiOriginSeries.origin_zero_degree
#print axioms OQ14.RiccatiOriginSeries.term_raising
#print axioms OQ14.RiccatiOriginSeries.term_raising_succ
#print axioms OQ14.RiccatiOriginSeries.origin_raising
#print axioms OQ14.RiccatiOriginSeries.origin_eq_psi
#print axioms OQ14.RiccatiOriginSeries.originD_eq_psiD
#print axioms OQ14.RiccatiOriginSeries.psi_hasSum
#print axioms OQ14.RiccatiOriginSeries.origin_analyticAt

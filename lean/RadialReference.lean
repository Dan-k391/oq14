import RadialGluing

/-! Exact constant-coefficient reference radial propagation and quarter-wave pairs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.RadialReference

open Real OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack

def matrix (q σ t : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) : RealTransfer where
  a := Real.cos (q*t)
  b := σ/q*Real.sin (q*t)
  c := -q/σ*Real.sin (q*t)
  d := Real.cos (q*t)
  det_one := by
    field_simp [hq,hσ]
    linear_combination (q*σ)*(Real.cos_sq_add_sin_sq (q*t))

def solution (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (s : State) (t : ℝ) : State :=
  act (matrix q σ t hq hσ) s

theorem solution_zero (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (s : State) :
    solution q σ hq hσ s 0 = s := by
  apply Prod.ext <;> simp [solution,act,matrix]

theorem matrix_ode (q σ t : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) :
    HasDerivAt (fun t => (matrix q σ t hq hσ).a) (σ*(matrix q σ t hq hσ).c) t ∧
    HasDerivAt (fun t => (matrix q σ t hq hσ).b) (σ*(matrix q σ t hq hσ).d) t ∧
    HasDerivAt (fun t => (matrix q σ t hq hσ).c) ((-q^2/σ)*(matrix q σ t hq hσ).a) t ∧
    HasDerivAt (fun t => (matrix q σ t hq hσ).d) ((-q^2/σ)*(matrix q σ t hq hσ).b) t := by
  have hs := (Real.hasDerivAt_sin (q*t)).comp t ((hasDerivAt_id t).const_mul q)
  have hc := (Real.hasDerivAt_cos (q*t)).comp t ((hasDerivAt_id t).const_mul q)
  refine ⟨?_,?_,?_,?_⟩
  · convert hc using 1
    dsimp only [matrix]
    field_simp [hq,hσ]
    ring
  · convert hs.const_mul (σ/q) using 1
    dsimp only [matrix]
    field_simp [hq,hσ]
    ring
  · convert hs.const_mul (-q/σ) using 1
    dsimp only [matrix]
    field_simp [hq,hσ]
    ring
  · convert hc using 1
    dsimp only [matrix]
    field_simp [hq,hσ]
    ring

theorem solution_ode (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (s : State) (t : ℝ) :
    HasDerivAt (fun t => (solution q σ hq hσ s t).1)
      ((σ : ℂ)*(solution q σ hq hσ s t).2) t ∧
    HasDerivAt (fun t => (solution q σ hq hσ s t).2)
      (((-q^2/σ : ℝ) : ℂ)*(solution q σ hq hσ s t).1) t := by
  obtain ⟨ha,hb,hc,hd⟩ := matrix_ode q σ t hq hσ
  constructor
  · convert (ha.ofReal_comp.mul_const s.1).add (hb.ofReal_comp.mul_const s.2) using 1
    simp only [solution,act,Complex.ofReal_mul]
    ring
  · convert (hc.ofReal_comp.mul_const s.1).add (hd.ofReal_comp.mul_const s.2) using 1
    simp only [solution,act,Complex.ofReal_mul]
    ring

theorem quarter_wave (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) :
    (matrix q σ (Real.pi/(2*q)) hq hσ).a = 0 ∧
    (matrix q σ (Real.pi/(2*q)) hq hσ).b = σ/q ∧
    (matrix q σ (Real.pi/(2*q)) hq hσ).c = -q/σ ∧
    (matrix q σ (Real.pi/(2*q)) hq hσ).d = 0 := by
  have he : q*(Real.pi/(2*q))=Real.pi/2 := by field_simp [hq]; ring
  simp [matrix,he]

def pair (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) : RealTransfer :=
  compose (matrix 1 1 (Real.pi/2) one_ne_zero one_ne_zero)
    (matrix q σ (Real.pi/(2*q)) hq hσ)

theorem pair_diagonal (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) :
    (pair q σ hq hσ).a = -q/σ ∧ (pair q σ hq hσ).b = 0 ∧
    (pair q σ hq hσ).c = 0 ∧ (pair q σ hq hσ).d = -σ/q := by
  obtain ⟨ha,hb,hc,hd⟩ := quarter_wave q σ hq hσ
  have he : q*(Real.pi/(2*q))=Real.pi/2 := by field_simp [hq]; ring
  simp [pair,compose,matrix,he,neg_div]

def power (m : RealTransfer) : ℕ → RealTransfer
  | 0 => matrix 1 1 0 one_ne_zero one_ne_zero
  | n+1 => compose m (power m n)

theorem power_diagonal (m : RealTransfer) (hb : m.b=0) (hc : m.c=0) (n : ℕ) :
    (power m n).a = m.a^n ∧ (power m n).b = 0 ∧
    (power m n).c = 0 ∧ (power m n).d = m.d^n := by
  induction n with
  | zero => simp [power,matrix]
  | succ n ih =>
    obtain ⟨ha,hb',hc',hd⟩ := ih
    simp [power,compose,ha,hb,hb',hc,hc',hd,pow_succ,mul_comm]

theorem paired_power (q σ : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (n : ℕ) :
    (power (pair q σ hq hσ) n).a = (-q/σ)^n ∧
    (power (pair q σ hq hσ) n).b = 0 ∧
    (power (pair q σ hq hσ) n).c = 0 ∧
    (power (pair q σ hq hσ) n).d = (-σ/q)^n := by
  obtain ⟨ha,hb,hc,hd⟩ := pair_diagonal q σ hq hσ
  simpa only [ha,hd] using power_diagonal (pair q σ hq hσ) hb hc n

end OQ14.RadialReference

#print axioms OQ14.RadialReference.solution_zero
#print axioms OQ14.RadialReference.matrix_ode
#print axioms OQ14.RadialReference.solution_ode
#print axioms OQ14.RadialReference.quarter_wave
#print axioms OQ14.RadialReference.pair_diagonal
#print axioms OQ14.RadialReference.power_diagonal
#print axioms OQ14.RadialReference.paired_power

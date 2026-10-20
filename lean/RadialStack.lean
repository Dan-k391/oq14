import RadialPropagation

/-! Actual finite sequences of radial-layer transfers and outgoing loads.
Each layer is the explicit homogeneous solution. Chain records exact shared
radii; full spatial Maxwell realization is separate from these estimates. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.RadialStack

open Complex OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialPropagation
  OQ14.HankelEnergy OQ14.HankelRealBasis OQ14.ModalAlgebra
open scoped ComplexConjugate

abbrev State := ℂ × ℂ

def act (m : RealTransfer) (s : State) : State :=
  ((m.a : ℂ)*s.1+(m.b : ℂ)*s.2,(m.c : ℂ)*s.1+(m.d : ℂ)*s.2)

def imaginaryLoad (s : State) : ℝ := (s.2*conj s.1).im

theorem imaginaryLoad_act (m : RealTransfer) (s : State) :
    imaginaryLoad (act m s) = imaginaryLoad s := by
  simp only [imaginaryLoad,act,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  linear_combination (s.1.re*s.2.im-s.1.im*s.2.re)*m.det_one

structure Layer where
  q : ℝ
  σ : ℝ
  a : ℝ
  b : ℝ
  q_pos : 0 < q
  σ_pos : 0 < σ
  a_pos : 0 < a
  ordered : a ≤ b

def back (l : ℕ) (g : Layer) (s : State) : State :=
  act (transfer l g.q g.σ g.b g.a g.q_pos.ne' g.σ_pos.ne'
    (ne_of_gt (g.a_pos.trans_le g.ordered)) g.a_pos.ne') s

def wave (l : ℕ) (g : Layer) (s : State) (x : ℝ) : ℂ :=
  value l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
    (initialBeta l g.q g.σ g.b s.1 s.2) x

def waveMomentum (l : ℕ) (g : Layer) (s : State) (x : ℝ) : ℂ :=
  momentum l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
    (initialBeta l g.q g.σ g.b s.1 s.2) x

theorem wave_outer (l : ℕ) (g : Layer) (s : State) :
    wave l g s g.b = s.1 ∧ waveMomentum l g s g.b = s.2 :=
  ⟨initial_value l g.q g.σ g.b s.1 s.2 g.q_pos.ne' g.σ_pos.ne'
    (ne_of_gt (g.a_pos.trans_le g.ordered)),
    initial_momentum l g.q g.σ g.b s.1 s.2 g.q_pos.ne' g.σ_pos.ne'
      (ne_of_gt (g.a_pos.trans_le g.ordered))⟩

theorem wave_inner (l : ℕ) (g : Layer) (s : State) :
    wave l g s g.a = (back l g s).1 ∧ waveMomentum l g s g.a = (back l g s).2 :=
  ⟨transfer_value l g.q g.σ g.b g.a s.1 s.2 g.q_pos.ne' g.σ_pos.ne'
    (ne_of_gt (g.a_pos.trans_le g.ordered)) g.a_pos.ne',
    transfer_momentum l g.q g.σ g.b g.a s.1 s.2 g.q_pos.ne' g.σ_pos.ne'
      (ne_of_gt (g.a_pos.trans_le g.ordered)) g.a_pos.ne'⟩

def cost (l : ℕ) (g : Layer) : ℝ := generatorBound l g.q g.σ g.a*(g.b-g.a)

theorem back_energy (l : ℕ) (g : Layer) (s : State) :
    energy (back l g s).1 (back l g s).2 ≤ Real.exp (cost l g)*energy s.1 s.2 := by
  have h := (actual_layer_energy_bound l g.q g.σ
    (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
    g.a g.b g.q_pos.ne' g.σ_pos g.a_pos g.ordered).2
  change energy (wave l g s g.a) (waveMomentum l g s g.a) ≤
    Real.exp (cost l g)*energy (wave l g s g.b) (waveMomentum l g s g.b) at h
  rwa [(wave_outer l g s).1,(wave_outer l g s).2,
    (wave_inner l g s).1,(wave_inner l g s).2] at h

theorem back_load (l : ℕ) (g : Layer) (s : State)
    (hbarrier : g.q^2*g.b^2 ≤ angular l) (hs : radialLoad s.1 s.2 ≤ 0) :
    radialLoad (back l g s).1 (back l g s).2 ≤ 0 := by
  have hout : radialLoad (wave l g s g.b) (waveMomentum l g s g.b) ≤ 0 := by
    rwa [(wave_outer l g s).1,(wave_outer l g s).2]
  have h := (actual_layer_barrier l g.q g.σ
    (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
    g.a g.b g.q_pos.ne' g.σ_pos g.a_pos g.ordered hbarrier hout).1
    ⟨le_rfl,g.ordered⟩ ⟨g.ordered,le_rfl⟩ g.ordered
  change radialLoad (wave l g s g.a) (waveMomentum l g s g.a) ≤
    radialLoad (wave l g s g.b) (waveMomentum l g s g.b) at h
  rw [(wave_outer l g s).1,(wave_outer l g s).2,
    (wave_inner l g s).1,(wave_inner l g s).2] at h
  exact h.trans hs

def traverse (l : ℕ) : List Layer → State → State
  | [], s => s
  | g::gs, s => traverse l gs (back l g s)

def totalCost (l : ℕ) (gs : List Layer) : ℝ := (gs.map (cost l)).sum

theorem traverse_imaginaryLoad (l : ℕ) (gs : List Layer) (s : State) :
    imaginaryLoad (traverse l gs s) = imaginaryLoad s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [traverse,ih]
    exact imaginaryLoad_act _ _

theorem traverse_energy (l : ℕ) (gs : List Layer) (s : State) :
    energy (traverse l gs s).1 (traverse l gs s).2 ≤
      Real.exp (totalCost l gs)*energy s.1 s.2 := by
  induction gs generalizing s with
  | nil => simp [traverse,totalCost]
  | cons g gs ih =>
    change energy (traverse l gs (back l g s)).1 (traverse l gs (back l g s)).2 ≤ _
    apply (ih (back l g s)).trans
    apply (mul_le_mul_of_nonneg_left (back_energy l g s) (Real.exp_pos _).le).trans_eq
    simp only [totalCost,List.map_cons,List.sum_cons,Real.exp_add]
    ring

theorem traverse_load (l : ℕ) (gs : List Layer) (s : State)
    (hbarrier : ∀ g ∈ gs, g.q^2*g.b^2 ≤ angular l) (hs : radialLoad s.1 s.2 ≤ 0) :
    radialLoad (traverse l gs s).1 (traverse l gs s).2 ≤ 0 := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    exact ih (back l g s) (fun x hx => hbarrier x (List.mem_cons_of_mem _ hx))
      (back_load l g s (hbarrier g (List.mem_cons_self)) hs)

def outgoing (l : ℕ) (X : ℝ) : State := (xi l X,xiD l X)

theorem outgoing_imaginaryLoad (l : ℕ) (X : ℝ) (hX : 0 < X) :
    imaginaryLoad (outgoing l X) = 1 := by
  have h := real_wronskian l X hX.ne'
  simp only [imaginaryLoad,outgoing,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  dsimp only [regular,regularD,irregular,irregularD] at h
  linear_combination h

theorem outgoing_traverse_nonzero (l : ℕ) (gs : List Layer) (X : ℝ) (hX : 0 < X) :
    (traverse l gs (outgoing l X)).1 ≠ 0 := by
  intro hz
  have h := (traverse_imaginaryLoad l gs (outgoing l X)).trans (outgoing_imaginaryLoad l X hX)
  simp [imaginaryLoad,hz] at h

theorem outgoing_traverse_load (l : ℕ) (gs : List Layer) (X : ℝ) (hX : 0 < X)
    (hbarrier : ∀ g ∈ gs, g.q^2*g.b^2 ≤ angular l) :
    radialLoad (traverse l gs (outgoing l X)).1 (traverse l gs (outgoing l X)).2 ≤ 0 :=
  traverse_load l gs (outgoing l X) hbarrier
    (OQ14.HankelPositive.outgoing_radialLoad_nonpositive l X hX)

theorem outgoing_traverse_logDerivative (l : ℕ) (gs : List Layer) (X : ℝ) (hX : 0 < X)
    (hbarrier : ∀ g ∈ gs, g.q^2*g.b^2 ≤ angular l) :
    ((traverse l gs (outgoing l X)).2/(traverse l gs (outgoing l X)).1).re ≤ 0 := by
  have h := outgoing_traverse_load l gs X hX hbarrier
  rw [Complex.div_re,← add_div]
  apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
  simpa only [radialLoad,Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,
    sub_neg_eq_add] using h

/-- The list runs from the outermost layer inward, with exact shared radii. -/
inductive Chain : List Layer → ℝ → ℝ → Prop
  | nil (R : ℝ) : Chain [] R R
  | cons (g : Layer) (gs : List Layer) (R : ℝ) :
      Chain gs g.a R → Chain (g::gs) g.b R

theorem chain_ordered {gs : List Layer} {X R : ℝ} (h : Chain gs X R) : R ≤ X := by
  induction h with
  | nil R => exact le_rfl
  | cons g gs R h ih => exact ih.trans g.ordered

theorem chain_width {gs : List Layer} {X R : ℝ} (h : Chain gs X R) :
    (gs.map (fun g => g.b-g.a)).sum = X-R := by
  induction h with
  | nil R => simp
  | cons g gs R h ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem generator_uniform_bound (l : ℕ) (q σ R a M A : ℝ)
    (hR : 0 < R) (hRa : R ≤ a) (hσ : 1 ≤ σ) (hσM : σ ≤ M)
    (hq : q^2 ≤ M) (hA : 0 ≤ A) (hν : angular l ≤ A*R^2) :
    generatorBound l q σ a ≤ 2*M+A := by
  have hσp : 0 < σ := by linarith
  have ha : 0 < a := hR.trans_le hRa
  have hM : 0 ≤ M := by linarith
  have hsq : R^2 ≤ a^2 := (sq_le_sq₀ hR.le ha.le).mpr hRa
  have hden : R^2 ≤ σ*a^2 := hsq.trans (by nlinarith [sq_nonneg a])
  have hfirst : angular l/(σ*a^2) ≤ A := by
    apply (div_le_iff₀ (by positivity : 0 < σ*a^2)).mpr
    exact hν.trans (mul_le_mul_of_nonneg_left hden hA)
  have hsecond : q^2/σ ≤ M := by
    apply (div_le_iff₀ hσp).mpr
    exact hq.trans (by nlinarith)
  unfold generatorBound
  linarith

theorem chain_cost_bound (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (M A : ℝ) (hR : 0 < R) (hA : 0 ≤ A) (hν : angular l ≤ A*R^2)
    (hparams : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    totalCost l gs ≤ (2*M+A)*(X-R) := by
  induction h with
  | nil R => simp [totalCost]
  | cons g gs R h ih =>
    have hp := hparams g List.mem_cons_self
    have hg := generator_uniform_bound l g.q g.σ R g.a M A hR
      (chain_ordered h) hp.1 hp.2.1 hp.2.2 hA hν
    have hc : cost l g ≤ (2*M+A)*(g.b-g.a) :=
      mul_le_mul_of_nonneg_right hg (sub_nonneg.mpr g.ordered)
    have ht := ih hR hν (fun x hx => hparams x (List.mem_cons_of_mem _ hx))
    change cost l g+totalCost l gs ≤ _
    nlinarith

theorem chain_energy_bound (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (M A : ℝ) (hR : 0 < R) (hA : 0 ≤ A) (hν : angular l ≤ A*R^2)
    (hparams : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    energy (traverse l gs s).1 (traverse l gs s).2 ≤
      Real.exp ((2*M+A)*(X-R))*energy s.1 s.2 :=
  (traverse_energy l gs s).trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (chain_cost_bound l h M A hR hA hν hparams))
    (energy_nonnegative s.1 s.2))

end OQ14.RadialStack

#print axioms OQ14.RadialStack.imaginaryLoad_act
#print axioms OQ14.RadialStack.wave_outer
#print axioms OQ14.RadialStack.wave_inner
#print axioms OQ14.RadialStack.back_energy
#print axioms OQ14.RadialStack.back_load
#print axioms OQ14.RadialStack.traverse_imaginaryLoad
#print axioms OQ14.RadialStack.traverse_energy
#print axioms OQ14.RadialStack.traverse_load
#print axioms OQ14.RadialStack.outgoing_imaginaryLoad
#print axioms OQ14.RadialStack.outgoing_traverse_nonzero
#print axioms OQ14.RadialStack.outgoing_traverse_load
#print axioms OQ14.RadialStack.outgoing_traverse_logDerivative
#print axioms OQ14.RadialStack.chain_ordered
#print axioms OQ14.RadialStack.chain_width
#print axioms OQ14.RadialStack.generator_uniform_bound
#print axioms OQ14.RadialStack.chain_cost_bound
#print axioms OQ14.RadialStack.chain_energy_bound

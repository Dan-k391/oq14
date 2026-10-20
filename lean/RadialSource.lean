import RadialStack
import HankelIntermediateBounds

/-! Actual outgoing continuation and source coefficients for a finite radial stack.
The definitions use the explicit layer matrices and the actual vacuum basis.
Spatial Maxwell fields and all-order Green convergence are separate results. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialSource

open Complex OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack
  OQ14.RadialPropagation OQ14.HankelRealBasis
open OQ14.HankelEnergy (angular)
open scoped ComplexConjugate

theorem act_inverse (m : RealTransfer) (s : State) : act m (act (inverse m) s) = s := by
  have hd : (m.a : ℂ)*m.d-(m.b : ℂ)*m.c=1 := by exact_mod_cast m.det_one
  apply Prod.ext
  · dsimp only [act,inverse]
    push_cast
    linear_combination s.1*hd
  · dsimp only [act,inverse]
    push_cast
    linear_combination s.2*hd

theorem act_energy (m : RealTransfer) (s : State) :
    energy (act m s).1 (act m s).2 ≤
      (m.a^2+m.b^2+m.c^2+m.d^2)*energy s.1 s.2 := by
  have hr := real_state_bound m.a m.b m.c m.d s.1.re s.2.re
  have hi := real_state_bound m.a m.b m.c m.d s.1.im s.2.im
  simp only [energy,act,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  nlinarith

def coefficients (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) : State :=
  act (inverse (fundamental l R hR.ne')) (traverse l gs (outgoing l X))

def gamma (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) : ℂ :=
  (coefficients l gs R X hR).1/(coefficients l gs R X hR).2

theorem coefficients_load (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    imaginaryLoad (coefficients l gs R X hR) = 1 := by
  rw [coefficients,imaginaryLoad_act,traverse_imaginaryLoad,outgoing_imaginaryLoad l X hX]

theorem coefficients_second_ne_zero (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) : (coefficients l gs R X hR).2 ≠ 0 := by
  intro hz
  have h := coefficients_load l gs R X hR hX
  simp [imaginaryLoad,hz] at h

theorem continuation (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) :
    act (fundamental l R hR.ne') (coefficients l gs R X hR) =
      traverse l gs (outgoing l X) := act_inverse _ _

theorem gamma_im (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    (gamma l gs R X hR).im = -1/Complex.normSq (coefficients l gs R X hR).2 := by
  have h := coefficients_load l gs R X hR hX
  simp only [imaginaryLoad,Complex.mul_im,Complex.conj_re,Complex.conj_im] at h
  rw [gamma,Complex.div_im,←sub_div]
  congr 1
  linear_combination -h

theorem gamma_im_negative (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) : (gamma l gs R X hR).im < 0 := by
  rw [gamma_im l gs R X hR hX]
  exact div_neg_of_neg_of_pos (by norm_num)
    (Complex.normSq_pos.mpr (coefficients_second_ne_zero l gs R X hR hX))

theorem gamma_energy_bound (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) :
    ‖gamma l gs R X hR‖ ≤ energy (coefficients l gs R X hR).1 (coefficients l gs R X hR).2 := by
  let s := coefficients l gs R X hR
  have hs : imaginaryLoad s = 1 := coefficients_load l gs R X hR hX
  have hb : 0 < ‖s.2‖ := norm_pos_iff.mpr (coefficients_second_ne_zero l gs R X hR hX)
  have hprod : 1 ≤ ‖s.2‖*‖s.1‖ := by
    have h := Complex.abs_im_le_norm (s.2*conj s.1)
    rw [←imaginaryLoad,hs,abs_one,norm_mul,norm_conj] at h
    exact h
  change ‖s.1/s.2‖ ≤ energy s.1 s.2
  rw [norm_div]
  apply (div_le_iff₀ hb).mpr
  have hm := mul_le_mul_of_nonneg_right hprod (norm_nonneg s.1)
  have he : ‖s.1‖^2 ≤ energy s.1 s.2 := by
    rw [energy,Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg ‖s.2‖]
  nlinarith [mul_le_mul_of_nonneg_right he hb.le]

theorem coefficients_energy_bound (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) :
    energy (coefficients l gs R X hR).1 (coefficients l gs R X hR).2 ≤
      frobeniusSq l R*Real.exp (totalCost l gs)*frobeniusSq l X := by
  have h := act_energy (inverse (fundamental l R hR.ne')) (traverse l gs (outgoing l X))
  have hf : (inverse (fundamental l R hR.ne')).a^2+
      (inverse (fundamental l R hR.ne')).b^2+
      (inverse (fundamental l R hR.ne')).c^2+
      (inverse (fundamental l R hR.ne')).d^2 = frobeniusSq l R := by
    dsimp [inverse,fundamental,frobeniusSq]
    ring
  rw [hf] at h
  have hF : 0 ≤ frobeniusSq l R := by rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have ht := traverse_energy l gs (outgoing l X)
  have hx : energy (outgoing l X).1 (outgoing l X).2 = frobeniusSq l X :=
    (frobeniusSq_eq l X).symm
  rw [hx] at ht
  exact h.trans ((mul_le_mul_of_nonneg_left ht hF).trans_eq (by ring))

theorem gamma_stack_bound (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) :
    ‖gamma l gs R X hR‖ ≤ frobeniusSq l R*Real.exp (totalCost l gs)*frobeniusSq l X :=
  (gamma_energy_bound l gs R X hR hX).trans (coefficients_energy_bound l gs R X hR)

theorem gamma_low_range (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (M c : ℝ) (hR : 0 < R) (hc : c^2 < 1) (hν : angular l ≤ c^2*R^2)
    (hparams : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) :
    ‖gamma l gs R X hR‖ ≤ (4/(1-c^2))^2*Real.exp ((2*M+c^2)*(X-R)) := by
  have hRX := chain_ordered h
  have hX := hR.trans_le hRX
  have hRbound := low_range_frobeniusSq l c R R hc hR le_rfl hν
  have hXbound := low_range_frobeniusSq l c R X hc hR hRX hν
  have hcost := Real.exp_le_exp.mpr (chain_cost_bound l h M (c^2) hR (sq_nonneg c) hν hparams)
  have hC : 0 ≤ 4/(1-c^2) := div_nonneg (by norm_num) (by linarith)
  have hFr : 0 ≤ frobeniusSq l R := by rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hFx : 0 ≤ frobeniusSq l X := by rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  apply (gamma_stack_bound l gs R X hR hX).trans
  apply (mul_le_mul (mul_le_mul hRbound hcost (Real.exp_pos _).le
    hC) hXbound hFx (mul_nonneg hC (Real.exp_pos _).le)).trans_eq
  ring


def coreWave (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (x : ℝ) : ℂ :=
  (irregular l x : ℂ)+gamma l gs R X hR*regular l x

def coreWaveD (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (x : ℝ) : ℂ :=
  (irregularD l x : ℂ)+gamma l gs R X hR*regularD l x

theorem coreWave_ode (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (coreWave l gs R X hR) (coreWaveD l gs R X hR x) x ∧
    HasDerivAt (coreWaveD l gs R X hR)
      ((-(OQ14.HankelEnergy.weight l x) : ℂ)*coreWave l gs R X hR x) x := by
  obtain ⟨ha,hb⟩ := real_basis_hasDerivAt l x hx
  obtain ⟨hc,hd⟩ := real_basis_ode l x hx
  constructor
  · exact hb.ofReal_comp.add (ha.ofReal_comp.const_mul (gamma l gs R X hR))
  · convert hd.ofReal_comp.add (hc.ofReal_comp.const_mul (gamma l gs R X hR)) using 1
    simp only [coreWave,Complex.ofReal_mul,Complex.ofReal_neg]
    ring

theorem coreWave_wronskian (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : x ≠ 0) :
    (regular l x : ℂ)*coreWaveD l gs R X hR x-
      (regularD l x : ℂ)*coreWave l gs R X hR x = 1 := by
  have hw : (regular l x : ℂ)*irregularD l x-(irregular l x : ℂ)*regularD l x=1 := by
    exact_mod_cast real_wronskian l x hx
  dsimp only [coreWave,coreWaveD]
  linear_combination hw

theorem coreWave_boundary (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) :
    coreWave l gs R X hR R = (traverse l gs (outgoing l X)).1/(coefficients l gs R X hR).2 ∧
    coreWaveD l gs R X hR R = (traverse l gs (outgoing l X)).2/(coefficients l gs R X hR).2 := by
  have hm := continuation l gs R X hR
  have ha := congrArg Prod.fst hm
  have hb := congrArg Prod.snd hm
  have hβ := coefficients_second_ne_zero l gs R X hR hX
  change (regular l R : ℂ)*(coefficients l gs R X hR).1+
    (irregular l R : ℂ)*(coefficients l gs R X hR).2 = _ at ha
  change (regularD l R : ℂ)*(coefficients l gs R X hR).1+
    (irregularD l R : ℂ)*(coefficients l gs R X hR).2 = _ at hb
  constructor
  · rw [coreWave,gamma,←ha]
    field_simp
    ring
  · rw [coreWaveD,gamma,←hb]
    field_simp
    ring

def scalarGreen (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (x y : ℝ) : ℂ :=
  (regular l (min x y) : ℂ)*coreWave l gs R X hR (max x y)

theorem scalarGreen_formula (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (x y : ℝ) :
    scalarGreen l gs R X hR x y =
      (regular l (min x y) : ℂ)*irregular l (max x y)+
        gamma l gs R X hR*(regular l x : ℂ)*regular l y := by
  rcases le_total x y with h|h
  · simp only [scalarGreen,coreWave,min_eq_left h,max_eq_right h]
    ring
  · simp only [scalarGreen,coreWave,min_eq_right h,max_eq_left h]
    ring

theorem scalarGreen_jump (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (y : ℝ) (hy : y ≠ 0) :
    deriv (fun x : ℝ => (regular l y : ℂ)*coreWave l gs R X hR x) y-
    deriv (fun x : ℝ => (regular l x : ℂ)*coreWave l gs R X hR y) y = 1 := by
  rw [((coreWave_ode l gs R X hR y hy).1.const_mul (regular l y : ℂ)).deriv,
    ((real_basis_hasDerivAt l y hy).1.ofReal_comp.mul_const (coreWave l gs R X hR y)).deriv]
  exact coreWave_wronskian l gs R X hR y hy

end OQ14.RadialSource

#print axioms OQ14.RadialSource.act_inverse
#print axioms OQ14.RadialSource.act_energy
#print axioms OQ14.RadialSource.coefficients_load
#print axioms OQ14.RadialSource.coefficients_second_ne_zero
#print axioms OQ14.RadialSource.continuation
#print axioms OQ14.RadialSource.gamma_im
#print axioms OQ14.RadialSource.gamma_im_negative
#print axioms OQ14.RadialSource.gamma_energy_bound
#print axioms OQ14.RadialSource.coefficients_energy_bound
#print axioms OQ14.RadialSource.gamma_stack_bound
#print axioms OQ14.RadialSource.gamma_low_range
#print axioms OQ14.RadialSource.coreWave_ode
#print axioms OQ14.RadialSource.coreWave_wronskian
#print axioms OQ14.RadialSource.coreWave_boundary
#print axioms OQ14.RadialSource.scalarGreen_formula
#print axioms OQ14.RadialSource.scalarGreen_jump

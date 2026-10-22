import RadialBackwardLimit
import RadialSource

/-! Genuine fixed-degree outgoing source limits for a common finite stack. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialPhaseLimit
open Set Filter Complex OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack
  OQ14.RadialFiniteLimit OQ14.HankelRealBasis OQ14.ModalAlgebra
open scoped Topology ComplexConjugate

def radius (n : ℕ) : ℝ := 2*Real.pi*((n : ℝ)+1)
def phase (l : ℕ) : ℂ := (-I)^(l+1)
def normalizedOutgoing (l : ℕ) (R : ℝ) : State := (p l R,I*p l R+pD l R)

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity

theorem radius_tendsto : Tendsto radius atTop atTop := by
  exact (tendsto_atTop_add_const_right atTop (1 : ℝ)
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_mul_atTop
      (by positivity : 0 < 2*Real.pi)

theorem radius_exp (n : ℕ) : Complex.exp (I*(radius n : ℂ)) = 1 := by
  have he : I*(radius n : ℂ) = ((n+1 : ℕ) : ℂ)*(2*Real.pi*I) := by
    unfold radius
    push_cast
    ring
  rw [he]
  exact Complex.exp_nat_mul_two_pi_mul_I (n+1)

theorem phase_normSq (l : ℕ) : Complex.normSq (phase l) = 1 := by
  simp [phase,map_pow,Complex.normSq_neg]

theorem normalizedOutgoing_limit (l : ℕ) (d : ℝ) :
    Tendsto (fun R : ℝ => normalizedOutgoing l (R+d)) atTop (𝓝 (1,I)) := by
  have hp : Tendsto (fun R : ℝ => p l R) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit l 1 one_ne_zero I
  have hd : Tendsto (fun R : ℝ => pD l R) atTop (𝓝 0) := HankelEnergy.hankelPolyD_tendsto l I
  have h := hp.prodMk_nhds ((hp.const_mul I).add hd)
  simp only [mul_one,add_zero] at h
  exact h.comp (tendsto_atTop_add_const_right atTop d tendsto_id)

theorem outgoing_factorization (l : ℕ) (X : ℝ) :
    outgoing l X = (phase l*Complex.exp (I*(X : ℂ))) • normalizedOutgoing l X := rfl

theorem act_smul (m : RealTransfer) (c : ℂ) (s : State) : act m (c • s) = c • act m s := by
  apply Prod.ext <;> simp only [act,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem traverse_smul (l : ℕ) (gs : List Layer) (c : ℂ) (s : State) :
    traverse l gs (c • s) = c • traverse l gs s := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    change traverse l gs (act _ (c • s)) = _
    rw [act_smul,ih]
    rfl

def shape (l : ℕ) (R : ℝ) (s : State) : State :=
  ((irregularD l R : ℂ)*s.1-(irregular l R : ℂ)*s.2,
    -(regularD l R : ℂ)*s.1+(regular l R : ℂ)*s.2)

theorem shape_eq_act (l : ℕ) (R : ℝ) (hR : R ≠ 0) (s : State) :
    shape l R s = act (inverse (fundamental l R hR)) s := by
  apply Prod.ext <;> simp [shape,act,inverse,fundamental,sub_eq_add_neg]

def normalizedCoefficients (l : ℕ) (gs : List Segment) (R : ℝ) : State :=
  shape l R (RadialBackwardLimit.retreat l gs R (normalizedOutgoing l (R+width gs)))

theorem actual_gamma_normalized (l : ℕ) (gs : List Segment) (R : ℝ) (hR : 0 < R) :
    RadialSource.gamma l (layers gs R hR) R (R+width gs) hR =
      (normalizedCoefficients l gs R).1/(normalizedCoefficients l gs R).2 := by
  have hc : phase l*Complex.exp (I*((R+width gs : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) (Complex.exp_ne_zero _)
  rw [RadialSource.gamma,RadialSource.coefficients,outgoing_factorization,
    traverse_smul,act_smul]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  rw [mul_div_mul_left _ _ hc]
  rw [normalizedCoefficients,shape_eq_act l R hR.ne',RadialBackwardLimit.retreat_is_traverse]

def phaseBasis (l : ℕ) : RealTransfer where
  a := (phase l).re
  b := (phase l).im
  c := (phase l*I).re
  d := (phase l*I).im
  det_one := by
    have h := phase_normSq l
    simp only [Complex.normSq_apply] at h
    simp only [Complex.mul_re,Complex.mul_im,I_re,I_im,mul_zero,mul_one,zero_sub,zero_add]
    nlinarith

theorem vacuum_phase_limits (l : ℕ) :
    Tendsto (fun n : ℕ => xi l (radius n)) atTop (𝓝 (phase l)) ∧
    Tendsto (fun n : ℕ => xiD l (radius n)) atTop (𝓝 (phase l*I)) := by
  have h := (normalizedOutgoing_limit l 0).comp radius_tendsto
  simp only [add_zero] at h
  constructor
  · have ht := h.fst_nhds.const_mul (phase l)
    simp only [mul_one] at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun n => by simp [xi,phase,radius_exp,normalizedOutgoing])
  · have ht := h.snd_nhds.const_mul (phase l)
    apply ht.congr'
    exact Filter.Eventually.of_forall (fun n => by simp [xiD,phase,radius_exp,normalizedOutgoing])

theorem shape_limit (l : ℕ) (s : ℕ → State) (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun n => shape l (radius n) (s n)) atTop (𝓝 (act (inverse (phaseBasis l)) s₀)) := by
  obtain ⟨hu,hv⟩ := vacuum_phase_limits l
  have hur := Complex.continuous_re.tendsto _ |>.comp hu
  have hui := Complex.continuous_im.tendsto _ |>.comp hu
  have hvr := Complex.continuous_re.tendsto _ |>.comp hv
  have hvi := Complex.continuous_im.tendsto _ |>.comp hv
  have h := (((Complex.continuous_ofReal.tendsto _ |>.comp hvi).mul hs.fst_nhds).sub
    ((Complex.continuous_ofReal.tendsto _ |>.comp hui).mul hs.snd_nhds)).prodMk_nhds
    ((((Complex.continuous_ofReal.tendsto _ |>.comp hvr).neg).mul hs.fst_nhds).add
      ((Complex.continuous_ofReal.tendsto _ |>.comp hur).mul hs.snd_nhds))
  simpa only [shape,regular,regularD,irregular,irregularD,act,inverse,phaseBasis,
    Function.comp_def,Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using h

def limitingCoefficients (l : ℕ) (gs : List Segment) : State :=
  act (inverse (phaseBasis l)) (RadialBackwardLimit.reference gs (1,I))

theorem normalizedCoefficients_limit (l : ℕ) (gs : List Segment) :
    Tendsto (fun n => normalizedCoefficients l gs (radius n)) atTop (𝓝 (limitingCoefficients l gs)) := by
  have h := RadialBackwardLimit.finite_stack_limit l gs 0
    (fun R => normalizedOutgoing l (R+width gs)) (1,I) (normalizedOutgoing_limit l (width gs))
  simp only [add_zero] at h
  exact shape_limit l _ _ (h.comp radius_tendsto)

theorem reference_imaginaryLoad (gs : List Segment) (s : State) :
    imaginaryLoad (RadialBackwardLimit.reference gs s) = imaginaryLoad s := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change imaginaryLoad (act _ (RadialBackwardLimit.reference gs s)) = _
    rw [imaginaryLoad_act,ih]

theorem limiting_second_ne_zero (l : ℕ) (gs : List Segment) : (limitingCoefficients l gs).2 ≠ 0 := by
  have h : imaginaryLoad (limitingCoefficients l gs) = 1 := by
    rw [limitingCoefficients,imaginaryLoad_act,reference_imaginaryLoad]
    norm_num [imaginaryLoad]
  intro hz
  simp [imaginaryLoad,hz] at h

theorem actual_gamma_limit (l : ℕ) (gs : List Segment) :
    Tendsto (fun n : ℕ => RadialSource.gamma l (layers gs (radius n) (radius_pos n))
      (radius n) (radius n+width gs) (radius_pos n)) atTop
      (𝓝 ((limitingCoefficients l gs).1/(limitingCoefficients l gs).2)) := by
  have h := (normalizedCoefficients_limit l gs).fst_nhds.div
    (normalizedCoefficients_limit l gs).snd_nhds (limiting_second_ne_zero l gs)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n => (actual_gamma_normalized l gs (radius n) (radius_pos n)).symm)

end OQ14.RadialPhaseLimit

#print axioms OQ14.RadialPhaseLimit.radius_pos
#print axioms OQ14.RadialPhaseLimit.radius_tendsto
#print axioms OQ14.RadialPhaseLimit.radius_exp
#print axioms OQ14.RadialPhaseLimit.phase_normSq
#print axioms OQ14.RadialPhaseLimit.normalizedOutgoing_limit
#print axioms OQ14.RadialPhaseLimit.outgoing_factorization
#print axioms OQ14.RadialPhaseLimit.act_smul
#print axioms OQ14.RadialPhaseLimit.traverse_smul
#print axioms OQ14.RadialPhaseLimit.shape_eq_act
#print axioms OQ14.RadialPhaseLimit.actual_gamma_normalized
#print axioms OQ14.RadialPhaseLimit.vacuum_phase_limits
#print axioms OQ14.RadialPhaseLimit.shape_limit
#print axioms OQ14.RadialPhaseLimit.normalizedCoefficients_limit
#print axioms OQ14.RadialPhaseLimit.reference_imaginaryLoad
#print axioms OQ14.RadialPhaseLimit.limiting_second_ne_zero
#print axioms OQ14.RadialPhaseLimit.actual_gamma_limit

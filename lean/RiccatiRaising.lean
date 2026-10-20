import HankelPolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Degree raising for the actual finite Riccati--Hankel functions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RiccatiRaising

open Polynomial Complex OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.HankelPolynomial

theorem hankelCoeff_cross_degree (l s : ℕ) (phase : ℂ) :
    2*(s+1 : ℕ)*hankelCoeff (l+1) (s+1) phase =
      phase*(l+s+2 : ℕ)*(l+s+1 : ℕ)*hankelCoeff l s phase := by
  have hsp : (s : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  unfold hankelCoeff
  rw [show l+1+(s+1)=l+s+2 by omega,show l+1-(s+1)=l-s by omega]
  rw [Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,pow_succ,pow_succ]
  push_cast
  field_simp [factorial_cast_ne_zero,hsp]
  ring

theorem poly_coeff_raising (l s : ℕ) (phase : ℂ) :
    (poly (l+1) phase).coeff (s+1) = (poly l phase).coeff (s+1)+
      phase*(l+s+1 : ℕ)*(poly l phase).coeff s := by
  have htwo : (2*(s+1 : ℕ) : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero s)
  apply mul_left_cancel₀ htwo
  by_cases hs : s < l
  · rw [poly_coeff,poly_coeff,poly_coeff,if_pos (by omega),if_pos (by omega),if_pos (by omega)]
    have hc := hankelCoeff_cross_degree l s phase
    have hr := hankelCoeff_recurrence l s phase hs
    rw [Nat.cast_sub (Nat.le_of_lt hs)] at hr
    push_cast at hc hr ⊢
    linear_combination hc-hr
  · by_cases he : s = l
    · subst s
      rw [poly_coeff,poly_coeff,poly_coeff,if_pos (by omega),if_neg (by omega),if_pos le_rfl]
      have hc := hankelCoeff_cross_degree l l phase
      push_cast at hc ⊢
      linear_combination hc
    · have hs' : l < s := by omega
      simp [poly_coeff,not_le.mpr hs',show ¬s+1 ≤ l+1 by omega,show ¬s+1 ≤ l by omega]

theorem poly_raising (l : ℕ) (phase : ℂ) :
    poly (l+1) phase = poly l phase+C phase*(X*(C (l+1 : ℂ)*poly l phase+
      X*(poly l phase).derivative)) := by
  ext n
  cases n with
  | zero =>
    simp [poly_coeff,hankelCoeff,factorial_cast_ne_zero]
    rw [div_self (factorial_cast_ne_zero (l+1)),div_self (factorial_cast_ne_zero l)]
  | succ s =>
    simp only [coeff_add,coeff_C_mul,coeff_X_mul,euler_coeff]
    rw [poly_coeff_raising]
    push_cast
    ring

theorem inversePoly_raising (l : ℕ) (phase w : ℂ) :
    inversePoly (l+1) phase w = inversePoly l phase w+
      phase*w*((l+1 : ℕ)*inversePoly l phase w+w*inversePolyD l phase w) := by
  have hd : (poly l phase).derivative.eval w = inversePolyD l phase w := by
    have hp : HasDerivAt (inversePoly l phase) ((poly l phase).derivative.eval w) w := by
      convert (poly l phase).hasDerivAt w using 1
      funext z
      exact (poly_eval l phase z).symm
    exact hp.unique (inversePoly_hasDerivAt l phase w)
  have h := congrArg (fun p : Polynomial ℂ => p.eval w) (poly_raising l phase)
  simpa only [eval_add,eval_mul,eval_C,eval_X,poly_eval,hd,mul_assoc,Nat.cast_add,Nat.cast_one] using h

theorem hankelPoly_raising (l : ℕ) (phase z : ℂ) (hz : z ≠ 0) :
    hankelPoly (l+1) phase z = hankelPoly l phase z+
      phase/z*((l+1 : ℕ)*hankelPoly l phase z-z*hankelPolyD l phase z) := by
  have h := inversePoly_raising l phase z⁻¹
  have hd := inversePolyD_eq l phase z⁻¹ (inv_ne_zero hz)
  simp only [inv_inv] at hd
  have hD : inversePolyD l phase z⁻¹ = -z^2*hankelPolyD l phase z := by
    field_simp [hz] at hd
    simp only [one_div] at hd
    linear_combination hd
  simp only [inversePoly_eq,inv_inv,hD] at h
  convert h using 1
  field_simp [hz]
  ring

theorem xi_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    xi (l+1) z = (l+1 : ℕ)/z*xi l z-xiD l z := by
  unfold xi xiD p pD
  rw [pow_succ,hankelPoly_raising l I z hz]
  field_simp [hz]
  ring_nf
  simp [I_sq]
  ring

theorem xiMinus_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    xiMinus (l+1) z = (l+1 : ℕ)/z*xiMinus l z-xiMinusD l z := by
  unfold xiMinus xiMinusD pMinus pMinusD
  rw [pow_succ,hankelPoly_raising l (-I) z hz]
  field_simp [hz]
  ring_nf
  simp [I_sq]
  ring

theorem psi_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    psi (l+1) z = (l+1 : ℕ)/z*psi l z-psiD l z := by
  unfold psi psiD
  rw [xi_raising l z hz,xiMinus_raising l z hz]
  ring

theorem psi_zero_degree (z : ℂ) : psi 0 z = Complex.sin z := by
  norm_num [psi,xi,xiMinus,p,pMinus,hankelPoly,hankelCoeff,Complex.sin]
  simp only [mul_comm z I,neg_mul]
  ring

end OQ14.RiccatiRaising

#print axioms OQ14.RiccatiRaising.hankelCoeff_cross_degree
#print axioms OQ14.RiccatiRaising.poly_coeff_raising
#print axioms OQ14.RiccatiRaising.poly_raising
#print axioms OQ14.RiccatiRaising.inversePoly_raising
#print axioms OQ14.RiccatiRaising.hankelPoly_raising
#print axioms OQ14.RiccatiRaising.xi_raising
#print axioms OQ14.RiccatiRaising.xiMinus_raising
#print axioms OQ14.RiccatiRaising.psi_raising
#print axioms OQ14.RiccatiRaising.psi_zero_degree

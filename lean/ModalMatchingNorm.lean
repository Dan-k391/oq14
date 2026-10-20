import ModalMatching
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Actual derivative-pairing normalization of the matching residue

The left covector and right kernel vector are constructed from the actual
spherical matching entries. Their derivative pairing is the actual simple
determinant derivative. This is a boundary-pencil normalization, without
identification with a volume reciprocal Green norm.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalMatchingNorm

open Complex OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.ModalMatching

def curvature (l : ℕ) (z : ℂ) : ℂ := (l : ℂ)*(l+1)/z^2-1

def matchingDerivative (l : ℕ) (n z : ℂ) (v : Amplitudes) : Amplitudes :=
  (n^2*psiD l (n*z)*v.1-xiD l z*v.2,
    n*curvature l (n*z)*psi l (n*z)*v.1-curvature l z*xi l z*v.2)

def determinantDerivative (l : ℕ) (n z : ℂ) : ℂ :=
  (n^2-1)*psiD l (n*z)*xiD l z+
    n*psi l (n*z)*curvature l z*xi l z-
    n*xi l z*curvature l (n*z)*psi l (n*z)

theorem matching_hasDerivAt (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (v : Amplitudes) :
    HasDerivAt (fun w => matching l n w v) (matchingDerivative l n z v) z := by
  have hi := (hasDerivAt_id z).const_mul n
  have hp := (psi_hasDerivAt l (n*z) (mul_ne_zero hn hz)).comp z hi
  have hpd := (psiD_hasDerivAt l (n*z) (mul_ne_zero hn hz)).comp z hi
  have hx := xi_hasDerivAt l z hz
  have hxd := xiD_hasDerivAt l z hz
  convert (((hp.const_mul n).mul_const v.1).sub (hx.mul_const v.2)).prodMk
    ((hpd.mul_const v.1).sub (hxd.mul_const v.2)) using 1
  apply Prod.ext <;> dsimp [matchingDerivative, curvature] <;> ring

theorem determinant_hasDerivAt (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    HasDerivAt (tmDet l n) (determinantDerivative l n z) z := by
  have hi := (hasDerivAt_id z).const_mul n
  have hp := (psi_hasDerivAt l (n*z) (mul_ne_zero hn hz)).comp z hi
  have hpd := (psiD_hasDerivAt l (n*z) (mul_ne_zero hn hz)).comp z hi
  have hx := xi_hasDerivAt l z hz
  have hxd := xiD_hasDerivAt l z hz
  convert ((hp.const_mul n).mul hxd).sub (hx.mul hpd) using 1
  dsimp [tmDet, determinantDerivative, curvature]
  ring

theorem determinant_deriv (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    deriv (tmDet l n) z = determinantDerivative l n z :=
  (determinant_hasDerivAt l n z hn hz).deriv

def rightVector (l : ℕ) (n z : ℂ) : Amplitudes :=
  if xiD l z = 0 then adjugate l n z (0,1) else adjugate l n z (1,0)

def leftCovector (l : ℕ) (z : ℂ) : Amplitudes →L[ℂ] ℂ :=
  if xiD l z = 0 then ContinuousLinearMap.snd ℂ ℂ ℂ else
    ContinuousLinearMap.fst ℂ ℂ ℂ-(xi l z/xiD l z) • ContinuousLinearMap.snd ℂ ℂ ℂ

theorem rightVector_nonzero (l : ℕ) (n z : ℂ) (hz : z ≠ 0) : rightVector l n z ≠ 0 := by
  classical
  by_cases hxd : xiD l z = 0
  · have hx : xi l z ≠ 0 := (outgoing_state_nonzero l z hz).resolve_right (not_ne_iff.mpr hxd)
    intro hv
    have h1 := congrArg Prod.fst hv
    simp [rightVector, hxd, adjugate, hx] at h1
  · intro hv
    have h1 := congrArg Prod.fst hv
    simp [rightVector, hxd, adjugate] at h1

theorem leftCovector_nonzero (l : ℕ) (z : ℂ) : leftCovector l z ≠ 0 := by
  classical
  by_cases hxd : xiD l z = 0
  · intro hw
    have h := congrArg (fun w : Amplitudes →L[ℂ] ℂ => w (0,1)) hw
    simp [leftCovector, hxd] at h
  · intro hw
    have h := congrArg (fun w : Amplitudes →L[ℂ] ℂ => w (1,0)) hw
    simp [leftCovector, hxd] at h

theorem rightVector_kernel (l : ℕ) (n z : ℂ) (hd : tmDet l n z = 0) :
    matching l n z (rightVector l n z) = 0 := by
  classical
  by_cases hxd : xiD l z = 0 <;>
    simp only [rightVector, hxd, ↓reduceIte, matching_adjugate, hd, zero_mul, Prod.zero_eq_mk]

theorem leftCovector_kernel (l : ℕ) (n z : ℂ) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (v : Amplitudes) :
    leftCovector l z (matching l n z v) = 0 := by
  classical
  by_cases hxd : xiD l z = 0
  · have hx : xi l z ≠ 0 := (outgoing_state_nonzero l z hz).resolve_right (not_ne_iff.mpr hxd)
    have hp : psiD l (n*z) = 0 := by
      have h := hd
      simp only [tmDet, hxd, mul_zero, zero_sub] at h
      exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left hx
    simp [leftCovector, hxd, matching, hp]
  · simp only [leftCovector, hxd, ↓reduceIte, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, matching]
    field_simp
    dsimp [tmDet] at hd
    linear_combination v.1*hd

theorem adjugate_factor (l : ℕ) (n z : ℂ) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (f : Amplitudes) :
    adjugate l n z f = leftCovector l z f • rightVector l n z := by
  classical
  by_cases hxd : xiD l z = 0
  · have hx : xi l z ≠ 0 := (outgoing_state_nonzero l z hz).resolve_right (not_ne_iff.mpr hxd)
    have hp : psiD l (n*z) = 0 := by
      have h := hd
      simp only [tmDet, hxd, mul_zero, zero_sub] at h
      exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left hx
    apply Prod.ext <;> simp [rightVector, leftCovector, hxd, hp, adjugate, smul_eq_mul] <;> ring
  · apply Prod.ext
    · simp only [rightVector, leftCovector, hxd, ↓reduceIte, adjugate,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        Prod.smul_fst, smul_eq_mul]
      field_simp
      ring
    · simp only [rightVector, leftCovector, hxd, ↓reduceIte, adjugate,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        Prod.smul_snd, smul_eq_mul]
      field_simp
      dsimp [tmDet] at hd
      linear_combination -f.2*hd

theorem derivative_pairing (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) :
    leftCovector l z (matchingDerivative l n z (rightVector l n z)) =
      deriv (tmDet l n) z := by
  classical
  rw [determinant_deriv l n z hn hz]
  by_cases hxd : xiD l z = 0
  · simp [leftCovector, rightVector, hxd, matchingDerivative, adjugate, determinantDerivative]
    ring
  · simp only [leftCovector, rightVector, hxd, ↓reduceIte, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, matchingDerivative, adjugate]
    simp only [mul_one, mul_zero, sub_zero]
    unfold determinantDerivative
    field_simp
    dsimp [tmDet] at hd
    linear_combination -(curvature l z*xi l z)*hd

theorem derivative_pairing_nonzero (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (hs : deriv (tmDet l n) z ≠ 0) :
    leftCovector l z (matchingDerivative l n z (rightVector l n z)) ≠ 0 := by
  rw [derivative_pairing l n z hn hz hd]
  exact hs

theorem residue_normalized (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (f : Amplitudes) :
    residue l n z f =
      (leftCovector l z f /
        leftCovector l z (matchingDerivative l n z (rightVector l n z))) • rightVector l n z := by
  rw [derivative_pairing l n z hn hz hd]
  have hf := adjugate_factor l n z hz hd f
  have hr : residue l n z f = ((deriv (tmDet l n) z)⁻¹) • adjugate l n z f := by
    apply Prod.ext <;> simp [residue, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hr, hf, smul_smul]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

theorem matching_smul (l : ℕ) (n z a : ℂ) (v : Amplitudes) :
    matching l n z (a • v) = a • matching l n z v := by
  apply Prod.ext <;> simp [matching, smul_eq_mul] <;> ring

theorem matchingDerivative_smul (l : ℕ) (n z a : ℂ) (v : Amplitudes) :
    matchingDerivative l n z (a • v) = a • matchingDerivative l n z v := by
  apply Prod.ext <;> simp [matchingDerivative, smul_eq_mul] <;> ring

theorem derivative_pairing_rescale (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (a b : ℂ) :
    (b • leftCovector l z) (matchingDerivative l n z (a • rightVector l n z)) =
      (a*b)*deriv (tmDet l n) z := by
  rw [matchingDerivative_smul, ContinuousLinearMap.smul_apply, map_smul,
    derivative_pairing l n z hn hz hd]
  simp only [smul_eq_mul]
  ring

/-- Simultaneously scaling the actual right mode and left covector by one
nonzero scalar makes their derivative pairing one and keeps the residue
as their exact tensor product. -/
theorem exists_unit_derivative_pairing (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (hs : deriv (tmDet l n) z ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ a • rightVector l n z ≠ 0 ∧ a • leftCovector l z ≠ 0 ∧
      matching l n z (a • rightVector l n z) = 0 ∧
      (∀ v : Amplitudes, (a • leftCovector l z) (matching l n z v) = 0) ∧
      (a • leftCovector l z) (matchingDerivative l n z (a • rightVector l n z)) = 1 ∧
      (∀ f : Amplitudes, residue l n z f =
        (a • leftCovector l z) f • (a • rightVector l n z)) := by
  let d := deriv (tmDet l n) z
  have hd0 : d ≠ 0 := hs
  let a := Complex.exp (Complex.log d⁻¹/2)
  have ha : a ≠ 0 := Complex.exp_ne_zero _
  have ha2 : a^2 = d⁻¹ := by
    dsimp only [a]
    rw [pow_two, ← Complex.exp_add,
      show Complex.log d⁻¹/2+Complex.log d⁻¹/2 = Complex.log d⁻¹ by ring,
      Complex.exp_log (inv_ne_zero hd0)]
  refine ⟨a,ha,smul_ne_zero ha (rightVector_nonzero l n z hz),
    smul_ne_zero ha (leftCovector_nonzero l z), ?_, ?_, ?_, ?_⟩
  · rw [matching_smul, rightVector_kernel l n z hd, smul_zero]
  · intro v
    rw [ContinuousLinearMap.smul_apply, leftCovector_kernel l n z hz hd v, smul_zero]
  · rw [derivative_pairing_rescale l n z hn hz hd, ← pow_two, ha2]
    exact inv_mul_cancel₀ hd0
  · intro f
    rw [residue_normalized l n z hn hz hd f, derivative_pairing l n z hn hz hd,
      ContinuousLinearMap.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    change leftCovector l z f/d = (a*leftCovector l z f)*a
    rw [div_eq_mul_inv, ← ha2]
    ring

theorem exists_high_quality_normalized_matching_residue (l : ℕ) (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ L < z.re ∧ z.im < 0 ∧
      Q < z.re / (-2*z.im) ∧
      ∃ a : ℂ, a ≠ 0 ∧ a • rightVector l (n : ℂ) z ≠ 0 ∧ a • leftCovector l z ≠ 0 ∧
        matching l (n : ℂ) z (a • rightVector l (n : ℂ) z) = 0 ∧
        (∀ v : Amplitudes, (a • leftCovector l z) (matching l (n : ℂ) z v) = 0) ∧
        (a • leftCovector l z)
          (matchingDerivative l (n : ℂ) z (a • rightVector l (n : ℂ) z)) = 1 ∧
        (∀ f : Amplitudes, residue l (n : ℂ) z f =
          (a • leftCovector l z) f • (a • rightVector l (n : ℂ) z)) := by
  obtain ⟨z,hz,hd,hs,hL,hi,hqual⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros l n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact ⟨z,hz,hd,hL,hi,hqual,exists_unit_derivative_pairing l (n : ℂ) z hn0 hz hd hs⟩

end OQ14.ModalMatchingNorm

#print axioms OQ14.ModalMatchingNorm.matching_hasDerivAt
#print axioms OQ14.ModalMatchingNorm.determinant_hasDerivAt
#print axioms OQ14.ModalMatchingNorm.determinant_deriv
#print axioms OQ14.ModalMatchingNorm.rightVector_nonzero
#print axioms OQ14.ModalMatchingNorm.leftCovector_nonzero
#print axioms OQ14.ModalMatchingNorm.rightVector_kernel
#print axioms OQ14.ModalMatchingNorm.leftCovector_kernel
#print axioms OQ14.ModalMatchingNorm.adjugate_factor
#print axioms OQ14.ModalMatchingNorm.derivative_pairing
#print axioms OQ14.ModalMatchingNorm.derivative_pairing_nonzero
#print axioms OQ14.ModalMatchingNorm.residue_normalized
#print axioms OQ14.ModalMatchingNorm.matching_smul
#print axioms OQ14.ModalMatchingNorm.matchingDerivative_smul
#print axioms OQ14.ModalMatchingNorm.derivative_pairing_rescale
#print axioms OQ14.ModalMatchingNorm.exists_unit_derivative_pairing
#print axioms OQ14.ModalMatchingNorm.exists_high_quality_normalized_matching_residue

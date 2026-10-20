import HankelEnergy

/-! # Actual real vacuum basis and uniform low-range state bounds -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.HankelRealBasis

open Complex OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.HankelEnergy
open scoped ComplexConjugate

theorem hankelCoeff_conj (l s : ℕ) (phase : ℂ) :
    conj (hankelCoeff l s phase) = hankelCoeff l s (conj phase) := by
  simp [hankelCoeff,map_ofNat]

theorem hankelPoly_conj (l : ℕ) (phase z : ℂ) :
    conj (hankelPoly l phase z) = hankelPoly l (conj phase) (conj z) := by
  simp only [hankelPoly,map_sum,map_mul,hankelCoeff_conj,map_zpow₀]

theorem hankelPolyD_conj (l : ℕ) (phase z : ℂ) :
    conj (hankelPolyD l phase z) = hankelPolyD l (conj phase) (conj z) := by
  simp [hankelPolyD,hankelCoeff_conj]

theorem xi_conj_real (l : ℕ) (r : ℝ) : conj (xi l r) = xiMinus l r := by
  simp [xi,xiMinus,p,pMinus,←Complex.exp_conj,hankelPoly_conj]

theorem xiD_conj_real (l : ℕ) (r : ℝ) : conj (xiD l r) = xiMinusD l r := by
  simp [xiD,xiMinusD,p,pMinus,pD,pMinusD,←Complex.exp_conj,
    hankelPoly_conj,hankelPolyD_conj]

def regular (l : ℕ) (r : ℝ) : ℝ := (xi l r).re
def regularD (l : ℕ) (r : ℝ) : ℝ := (xiD l r).re
def irregular (l : ℕ) (r : ℝ) : ℝ := (xi l r).im
def irregularD (l : ℕ) (r : ℝ) : ℝ := (xiD l r).im

theorem regular_eq_psi (l : ℕ) (r : ℝ) : (regular l r : ℂ) = psi l r := by
  rw [psi,←xi_conj_real]
  apply Complex.ext <;> simp [regular]

theorem regularD_eq_psiD (l : ℕ) (r : ℝ) : (regularD l r : ℂ) = psiD l r := by
  rw [psiD,←xiD_conj_real]
  apply Complex.ext <;> simp [regularD]

theorem real_wronskian (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    regular l r*irregularD l r-irregular l r*regularD l r = 1 := by
  have h := hankel_wronskian l (r : ℂ) (ofReal_ne_zero.mpr hr)
  rw [←xi_conj_real,←xiD_conj_real] at h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im] at hi
  norm_num at hi
  dsimp only [regular,regularD,irregular,irregularD]
  nlinarith

def fundamental (l : ℕ) (r : ℝ) (hr : r ≠ 0) : RadialGreen.RealTransfer where
  a := regular l r
  b := irregular l r
  c := regularD l r
  d := irregularD l r
  det_one := real_wronskian l r hr

theorem real_basis_hasDerivAt (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (regular l) (regularD l r) r ∧
      HasDerivAt (irregular l) (irregularD l r) r := by
  have h := (xi_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).comp_ofReal
  exact ⟨Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h,
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h⟩

theorem real_basis_ode (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (regularD l) (-weight l r*regular l r) r ∧
      HasDerivAt (irregularD l) (-weight l r*irregular l r) r := by
  have h := (xiD_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).comp_ofReal
  have he : (l : ℂ)*(l+1)/(r : ℂ)^2-1 = -(weight l r : ℂ) := by
    simp only [weight,angular,ofReal_sub,ofReal_div,ofReal_pow,ofReal_mul,
      ofReal_natCast,ofReal_add,ofReal_one]
    ring
  rw [he] at h
  constructor
  · simpa [regularD,regular] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  · simpa [irregularD,irregular] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h

def frobeniusSq (l : ℕ) (r : ℝ) : ℝ :=
  regular l r^2+irregular l r^2+regularD l r^2+irregularD l r^2

theorem frobeniusSq_eq (l : ℕ) (r : ℝ) :
    frobeniusSq l r = Complex.normSq (xi l r)+Complex.normSq (xiD l r) := by
  simp only [frobeniusSq,regular,irregular,regularD,irregularD,Complex.normSq_apply]
  ring

theorem low_range_frobeniusSq (l : ℕ) (c R r : ℝ)
    (hc : c^2 < 1) (hR : 0 < R) (hRr : R ≤ r)
    (hl : angular l ≤ c^2*R^2) : frobeniusSq l r ≤ 4/(1-c^2) := by
  obtain ⟨hd,hx⟩ := low_range_normSq_bounds l c R r hc hR hRr hl
  rw [frobeniusSq_eq]
  have hden : 0 < 1-c^2 := by linarith
  have h2 : 2 ≤ 2/(1-c^2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [sq_nonneg c]
  have he : 4/(1-c^2) = 2/(1-c^2)+2/(1-c^2) := by ring
  rw [he]
  exact add_le_add hx (hd.trans h2)

theorem real_state_bound (a b c d x y : ℝ) :
    (a*x+b*y)^2+(c*x+d*y)^2 ≤ (a^2+b^2+c^2+d^2)*(x^2+y^2) := by
  nlinarith [sq_nonneg (a*y-b*x),sq_nonneg (c*y-d*x)]

theorem low_range_state (l : ℕ) (c R r : ℝ)
    (hc : c^2 < 1) (hR : 0 < R) (hRr : R ≤ r)
    (hl : angular l ≤ c^2*R^2) (x y : ℝ) :
    (regular l r*x+irregular l r*y)^2+(regularD l r*x+irregularD l r*y)^2 ≤
      (4/(1-c^2))*(x^2+y^2) :=
  (real_state_bound _ _ _ _ x y).trans (mul_le_mul_of_nonneg_right
    (low_range_frobeniusSq l c R r hc hR hRr hl) (by positivity))

theorem low_range_inverse_state (l : ℕ) (c R r : ℝ)
    (hc : c^2 < 1) (hR : 0 < R) (hRr : R ≤ r)
    (hl : angular l ≤ c^2*R^2) (x y : ℝ) :
    (irregularD l r*x-irregular l r*y)^2+(-regularD l r*x+regular l r*y)^2 ≤
      (4/(1-c^2))*(x^2+y^2) := by
  have h := real_state_bound (irregularD l r) (-irregular l r) (-regularD l r)
    (regular l r) x y
  have hf : irregularD l r^2+(-irregular l r)^2+(-regularD l r)^2+regular l r^2 =
      frobeniusSq l r := by dsimp [frobeniusSq];ring
  rw [hf] at h
  have hb := h.trans (mul_le_mul_of_nonneg_right
    (low_range_frobeniusSq l c R r hc hR hRr hl) (by positivity : 0 ≤ x^2+y^2))
  simpa only [neg_mul,sub_eq_add_neg] using hb

end OQ14.HankelRealBasis

#print axioms OQ14.HankelRealBasis.hankelCoeff_conj
#print axioms OQ14.HankelRealBasis.hankelPoly_conj
#print axioms OQ14.HankelRealBasis.hankelPolyD_conj
#print axioms OQ14.HankelRealBasis.xi_conj_real
#print axioms OQ14.HankelRealBasis.xiD_conj_real
#print axioms OQ14.HankelRealBasis.regular_eq_psi
#print axioms OQ14.HankelRealBasis.regularD_eq_psiD
#print axioms OQ14.HankelRealBasis.real_wronskian
#print axioms OQ14.HankelRealBasis.real_basis_hasDerivAt
#print axioms OQ14.HankelRealBasis.real_basis_ode
#print axioms OQ14.HankelRealBasis.frobeniusSq_eq
#print axioms OQ14.HankelRealBasis.low_range_frobeniusSq
#print axioms OQ14.HankelRealBasis.real_state_bound
#print axioms OQ14.HankelRealBasis.low_range_state
#print axioms OQ14.HankelRealBasis.low_range_inverse_state

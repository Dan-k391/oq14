import ModalShellAnalytic
import ModalFieldResidue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order

/-! # Actual simple poles of the spherical shell response

The regularized response is constructed using the actual divided slope of
the TM determinant. Its analyticity, nonzero value, exact punctured normal
form and meromorphic order are proved. This is the two-data spherical
matching response with actual shell fields, not the full Maxwell resolvent.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalFieldPole

open Complex Filter OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.ModalMatching
  OQ14.ModalInterface OQ14.ModalShell OQ14.ModalShellAnalytic OQ14.ModalFieldResidue
open scoped Topology

def numeratorCoefficient (n k : ℂ) : Amplitudes →L[ℂ] ℂ :=
  psiD 1 (n*k) • ContinuousLinearMap.fst ℂ ℂ ℂ -
    (n*psi 1 (n*k)) • ContinuousLinearMap.snd ℂ ℂ ℂ

def numerator (n k : ℂ) : Amplitudes →L[ℂ] ShellL2 :=
  (numeratorCoefficient n k).smulRight (fieldL2 k)

def response (n k : ℂ) : Amplitudes →L[ℂ] ShellL2 :=
  (tmDet 1 n k)⁻¹ • numerator n k

def regularized (n k₀ k : ℂ) : Amplitudes →L[ℂ] ShellL2 :=
  (dslope (tmDet 1 n) k₀ k)⁻¹ • numerator n k

theorem numeratorCoefficient_apply (n k : ℂ) (f : Amplitudes) :
    numeratorCoefficient n k f = (adjugate 1 n k f).2 := rfl

theorem response_eq_actual (n : ℂ) (k : Frequency) :
    response n k.1 = responseOperator n k := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [response, numerator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, numeratorCoefficient_apply, fieldL2_eq_unit,
    responseOperator_apply, solve, smul_smul, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

theorem regularized_center (n : ℂ) (k₀ : Frequency) :
    regularized n k₀.1 k₀.1 = residueOperator n k₀ := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [regularized, dslope_same, numerator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, numeratorCoefficient_apply, fieldL2_eq_unit,
    residueOperator_apply, residue, smul_smul, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

theorem determinant_analytic (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    AnalyticAt ℂ (tmDet 1 n) k := by
  have hd : DifferentiableOn ℂ (tmDet 1 n) {0}ᶜ :=
    fun z hz => (tmDet_differentiableAt 1 n z hn hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hk)

theorem numeratorCoefficient_analytic (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    AnalyticAt ℂ (numeratorCoefficient n) k := by
  have hp : AnalyticAt ℂ (fun z => psi 1 (n*z)) k := by
    have hd : DifferentiableOn ℂ (fun z => psi 1 (n*z)) {0}ᶜ := by
      intro z hz
      exact ((psi_hasDerivAt 1 _ (mul_ne_zero hn hz)).differentiableAt.comp z
        ((differentiableAt_const n).mul differentiableAt_id)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hk)
  have hpD : AnalyticAt ℂ (fun z => psiD 1 (n*z)) k := by
    have hd : DifferentiableOn ℂ (fun z => psiD 1 (n*z)) {0}ᶜ := by
      intro z hz
      exact ((psiD_hasDerivAt 1 _ (mul_ne_zero hn hz)).differentiableAt.comp z
        ((differentiableAt_const n).mul differentiableAt_id)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hk)
  exact (hpD.smul analyticAt_const).sub
    ((analyticAt_const.mul hp).smul analyticAt_const)

theorem numerator_analytic (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    AnalyticAt ℂ (numerator n) k := by
  exact ((ContinuousLinearMap.smulRightL ℂ Amplitudes ShellL2).analyticAt_bilinear _).comp₂
    (numeratorCoefficient_analytic n k hn hk) (fieldL2_analytic k hk)

theorem response_analytic (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (hd : tmDet 1 n k ≠ 0) : AnalyticAt ℂ (response n) k :=
  ((determinant_analytic n k hn hk).inv hd).smul (numerator_analytic n k hn hk)

theorem determinant_dslope_analytic (n k₀ : ℂ) (hn : n ≠ 0) (hk : k₀ ≠ 0) :
    AnalyticAt ℂ (dslope (tmDet 1 n) k₀) k₀ := by
  obtain ⟨p,hp⟩ := determinant_analytic n k₀ hn hk
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem regularized_analytic (n k₀ : ℂ) (hn : n ≠ 0) (hk : k₀ ≠ 0)
    (hs : deriv (tmDet 1 n) k₀ ≠ 0) : AnalyticAt ℂ (regularized n k₀) k₀ :=
  ((determinant_dslope_analytic n k₀ hn hk).inv
    (by simpa only [dslope_same] using hs)).smul (numerator_analytic n k₀ hn hk)

theorem response_normal_form (n k₀ k : ℂ) (hd : tmDet 1 n k₀ = 0) (hk : k ≠ k₀) :
    response n k = (k-k₀)⁻¹ • regularized n k₀ k := by
  simp only [response, regularized, dslope_of_ne _ hk, slope_def_field, hd, sub_zero,
    inv_div, smul_smul]
  congr 1
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hk), one_mul]

theorem regularized_nonzero (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    regularized n k₀.1 k₀.1 ≠ 0 := by
  rw [regularized_center]
  exact residueOperator_nonzero n k₀ hn hd hs

theorem response_meromorphic (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) :
    MeromorphicAt (response n) k :=
  (determinant_analytic n k hn hk).meromorphicAt.inv.smul
    (numerator_analytic n k hn hk).meromorphicAt

theorem response_order_minus_one (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    (response_meromorphic n k₀.1 hn k₀.property).order = (-1 : ℤ) := by
  apply (MeromorphicAt.order_eq_int_iff _).mpr
  refine ⟨regularized n k₀.1, regularized_analytic n k₀.1 hn k₀.property hs,
    regularized_nonzero n k₀ hn hd hs, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with k hk
  simpa only [zpow_neg_one] using response_normal_form n k₀.1 k hd hk

theorem exists_high_quality_simple_field_poles (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k₀ : Frequency, L < k₀.1.re ∧ k₀.1.im < 0 ∧
      Q < k₀.1.re / (-2*k₀.1.im) ∧
      ∃ hm : MeromorphicAt (response (n : ℂ)) k₀.1,
        hm.order = (-1 : ℤ) ∧
        AnalyticAt ℂ (regularized (n : ℂ) k₀.1) k₀.1 ∧
        regularized (n : ℂ) k₀.1 k₀.1 = residueOperator (n : ℂ) k₀ ∧
        residueOperator (n : ℂ) k₀ ≠ 0 := by
  obtain ⟨k, hk, hd, hs, hL, hi, hratio⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros 1 n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact ⟨⟨k,hk⟩, hL, hi, hratio, response_meromorphic (n : ℂ) k hn0 hk,
    response_order_minus_one (n : ℂ) ⟨k,hk⟩ hn0 hd hs,
    regularized_analytic (n : ℂ) k hn0 hk hs, regularized_center (n : ℂ) ⟨k,hk⟩,
    residueOperator_nonzero (n : ℂ) ⟨k,hk⟩ hn0 hd hs⟩

end OQ14.ModalFieldPole


#print axioms OQ14.ModalFieldPole.numeratorCoefficient_apply
#print axioms OQ14.ModalFieldPole.response_eq_actual
#print axioms OQ14.ModalFieldPole.regularized_center
#print axioms OQ14.ModalFieldPole.determinant_analytic
#print axioms OQ14.ModalFieldPole.numeratorCoefficient_analytic
#print axioms OQ14.ModalFieldPole.numerator_analytic
#print axioms OQ14.ModalFieldPole.response_analytic
#print axioms OQ14.ModalFieldPole.determinant_dslope_analytic
#print axioms OQ14.ModalFieldPole.regularized_analytic
#print axioms OQ14.ModalFieldPole.response_normal_form
#print axioms OQ14.ModalFieldPole.regularized_nonzero
#print axioms OQ14.ModalFieldPole.response_meromorphic
#print axioms OQ14.ModalFieldPole.response_order_minus_one
#print axioms OQ14.ModalFieldPole.exists_high_quality_simple_field_poles

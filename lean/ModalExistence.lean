import ModalRational
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Constructive large-argument roots for the modal exponential equation

The analytic existence argument is developed using an actual contraction
in the inverse coordinate. No existence of a resonance is an assumption.
The physical operator identification remains a separate obligation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalExistence

open Complex Metric Set OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.ModalRational
open scoped NNReal

/-- An explicit inverse-coordinate contraction. It converts local
Lipschitz control into a large-argument solution, without a root premise. -/
theorem inverse_fixed_point (H : ℂ → ℂ) (C : ℝ≥0) (r : ℝ) (hr : 0 < r)
    (hH : LipschitzOnWith C H (closedBall 0 r)) (hzero : H 0 = 0)
    (z₀ : ℂ) (hz₀ : (C : ℝ) * r + 2 * C + 1 + r⁻¹ ≤ ‖z₀‖) :
    ∃ z : ℂ, z ≠ 0 ∧ z⁻¹ ∈ closedBall 0 r ∧
      z = z₀ + H z⁻¹ ∧ ‖z - z₀‖ ≤ C * r := by
  let f : ℂ → ℂ := fun w => (z₀ + H w)⁻¹
  have h0 : (0 : ℂ) ∈ closedBall 0 r := by simp [hr.le]
  have hbound (w : ℂ) (hw : w ∈ closedBall 0 r) : ‖H w‖ ≤ C * r := by
    have h := hH.dist_le_mul w hw 0 h0
    simp only [hzero, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hw) C.2)
  have hlower (w : ℂ) (hw : w ∈ closedBall 0 r) :
      2 * (C : ℝ) + 1 + r⁻¹ ≤ ‖z₀ + H w‖ := by
    have ht : ‖z₀‖ ≤ ‖z₀ + H w‖ + ‖H w‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (z₀ + H w) (H w)
    have hb := hbound w hw
    linarith
  have hpos (w : ℂ) (hw : w ∈ closedBall 0 r) : 0 < ‖z₀ + H w‖ := by
    have hp : 0 < 2 * (C : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) C.2) zero_lt_one
    exact (add_pos hp (inv_pos.mpr hr)).trans_le (hlower w hw)
  have hmap : MapsTo f (closedBall 0 r) (closedBall 0 r) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    dsimp [f]
    rw [norm_inv]
    apply (inv_le_comm₀ (hpos w hw) hr).2
    exact (le_add_of_nonneg_left
      (add_nonneg (mul_nonneg (by norm_num) C.2) zero_le_one)).trans (hlower w hw)
  have hdist (w v : ℂ) (hw : w ∈ closedBall 0 r) (hv : v ∈ closedBall 0 r) :
      dist (f w) (f v) ≤ (1 / 2 : ℝ) * dist w v := by
    have hpw := hpos w hw
    have hpv := hpos v hv
    have hnw : z₀ + H w ≠ 0 := norm_pos_iff.mp hpw
    have hnv : z₀ + H v ≠ 0 := norm_pos_iff.mp hpv
    have hden : 2 * (C : ℝ) ≤ ‖z₀ + H w‖ * ‖z₀ + H v‖ := by
      have hw' := hlower w hw
      have hv' := hlower v hv
      have hi := inv_pos.mpr hr
      have hC := C.2
      have hw1 : 2 * (C : ℝ) + 1 ≤ ‖z₀ + H w‖ := by linarith only [hw', hi]
      have hv1 : 2 * (C : ℝ) + 1 ≤ ‖z₀ + H v‖ := by linarith only [hv', hi]
      have hnonneg : 0 ≤ 2 * (C : ℝ) + 1 :=
        add_nonneg (mul_nonneg (by norm_num) C.2) zero_le_one
      have hmul := mul_le_mul hw1 hv1 hnonneg (norm_nonneg (z₀ + H w))
      nlinarith only [hmul, hC, sq_nonneg (C : ℝ)]
    dsimp [f]
    rw [dist_inv_inv₀ hnw hnv, dist_add_left]
    apply (div_le_iff₀ (mul_pos hpw hpv)).2
    have hh := hH.dist_le_mul w hw v hv
    have hd := dist_nonneg (x := w) (y := v)
    nlinarith
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmap.restrict f _ _) := by
    refine ⟨by exact_mod_cast (by norm_num : (1 : ℝ) / 2 < 1), LipschitzWith.of_dist_le_mul ?_⟩
    intro w v
    exact hdist w v w.property v.property
  obtain ⟨w, hw, hfix, -, -⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract h0 (edist_ne_top _ _)
  have harg : z₀ + H w ≠ 0 := norm_pos_iff.mp (hpos w hw)
  have hw0 : w ≠ 0 := by
    rw [← hfix]
    exact inv_ne_zero harg
  refine ⟨w⁻¹, inv_ne_zero hw0, by simpa only [inv_inv] using hw, ?_, ?_⟩
  · simpa only [f, inv_inv] using congrArg Inv.inv hfix.symm
  · rw [show w⁻¹ = z₀ + H w by simpa only [f, inv_inv] using congrArg Inv.inv hfix.symm]
    simpa only [add_sub_cancel_left] using hbound w hw

theorem polynomial_contDiff (p : Polynomial ℂ) :
    ContDiff ℂ 1 (fun w => p.eval w) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n c => simpa using contDiff_const.mul (contDiff_id.pow n)

/-- Every sufficiently distant exact constant-coefficient exponential
root has an actual nearby root of the inverse-polynomial equation. -/
theorem exponential_polynomial_nearby (A B : Polynomial ℂ) (a : ℂ)
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (ha : a ≠ 0) :
    ∃ R D : ℝ, ∀ z₀ : ℂ,
      exp (a * z₀) = -B.eval 0 / A.eval 0 → R ≤ ‖z₀‖ →
      ∃ z : ℂ, z ≠ 0 ∧ A.eval z⁻¹ ≠ 0 ∧
        exp (a * z) = -B.eval z⁻¹ / A.eval z⁻¹ ∧ ‖z - z₀‖ ≤ D := by
  let Q : ℂ → ℂ := fun w => -B.eval w / A.eval w
  have hQ0 : Q 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hA
  have hQ : ContDiffAt ℂ 1 Q 0 :=
    (polynomial_contDiff B).contDiffAt.neg.div (polynomial_contDiff A).contDiffAt hA
  let H : ℂ → ℂ := fun w => a⁻¹ * log (Q w / Q 0)
  have hratio : Q 0 / Q 0 = 1 := div_self hQ0
  have hlog : ContDiffAt ℂ 1 log (Q 0 / Q 0) := by
    rw [hratio]
    exact contDiffAt_log one_mem_slitPlane
  have hH : ContDiffAt ℂ 1 H 0 := by
    simpa only [H, Function.comp_def] using
      (contDiffAt_const (c := a⁻¹)).mul (hlog.comp 0 (hQ.div_const (Q 0)))
  have hH0 : H 0 = 0 := by simp [H, hratio]
  obtain ⟨C, t, ht, hCt⟩ := hH.exists_lipschitzOnWith
  have hQev : ∀ᶠ w in nhds (0 : ℂ), Q w ≠ 0 :=
    hQ.continuousAt.tendsto.eventually (eventually_ne_nhds hQ0)
  have hAev : ∀ᶠ w in nhds (0 : ℂ), A.eval w ≠ 0 :=
    (polynomial_contDiff A).continuous.continuousAt.tendsto.eventually (eventually_ne_nhds hA)
  have hregion : t ∩ {w : ℂ | Q w ≠ 0 ∧ A.eval w ≠ 0} ∈ nhds (0 : ℂ) :=
    Filter.inter_mem ht (hQev.and hAev)
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp hregion
  have hClip : LipschitzOnWith C H (closedBall 0 r) := hCt.mono (fun w hw => (hrt hw).1)
  refine ⟨C * r + 2 * C + 1 + r⁻¹, C * r, ?_⟩
  intro z₀ hbase hz₀
  obtain ⟨z, hz, hw, hsol, hdist⟩ := inverse_fixed_point H C r hr hClip hH0 z₀ hz₀
  have hwQ : Q z⁻¹ ≠ 0 := (hrt hw).2.1
  have hwA : A.eval z⁻¹ ≠ 0 := (hrt hw).2.2
  refine ⟨z, hz, hwA, ?_, hdist⟩
  change exp (a * z) = Q z⁻¹
  calc
    exp (a * z) = exp (a * z₀ + log (Q z⁻¹ / Q 0)) := by
      congr 1
      conv_lhs => rw [hsol]
      dsimp [H]
      field_simp [ha]
      ring
    _ = Q z⁻¹ := by
      rw [exp_add, hbase, exp_log (div_ne_zero hwQ hQ0)]
      change Q 0 * (Q z⁻¹ / Q 0) = Q z⁻¹
      field_simp [hQ0]

theorem unbounded_constant_exponential_roots (a q : ℂ) (ha : a ≠ 0) (hq : q ≠ 0)
    (R : ℝ) : ∃ z₀ : ℂ, exp (a * z₀) = q ∧ R < ‖z₀‖ := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨m, hm⟩ := exists_nat_gt ((R * ‖a‖ + ‖log q‖) / (2 * Real.pi))
  have hm' : R * ‖a‖ + ‖log q‖ < (m : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ hp).mp hm
  let u : ℂ := (m : ℂ) * (2 * Real.pi * I)
  have hu : ‖u‖ = (m : ℝ) * (2 * Real.pi) := by
    simp [u, norm_mul, abs_of_pos Real.pi_pos]
  have he : exp u = 1 := exp_nat_mul_two_pi_mul_I m
  refine ⟨(log q + u) / a, ?_, ?_⟩
  · rw [mul_div_cancel₀ _ ha, exp_add, exp_log hq, he, mul_one]
  · rw [norm_div]
    apply (lt_div_iff₀ (norm_pos_iff.mpr ha)).2
    have ht : ‖u‖ ≤ ‖log q + u‖ + ‖log q‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (log q + u) (log q)
    rw [hu] at ht
    linarith only [hm', ht]

/-- Actual roots occur at arbitrarily large modulus for every inverse
polynomial quotient with nonzero value at the origin. -/
theorem unbounded_exponential_polynomial_roots (A B : Polynomial ℂ) (a : ℂ)
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (ha : a ≠ 0) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ A.eval z⁻¹ ≠ 0 ∧
      exp (a * z) = -B.eval z⁻¹ / A.eval z⁻¹ ∧ L < ‖z‖ := by
  obtain ⟨R, D, hnear⟩ := exponential_polynomial_nearby A B a hA hB ha
  have hq : -B.eval 0 / A.eval 0 ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hA
  obtain ⟨z₀, hb, hnorm⟩ := unbounded_constant_exponential_roots a _ ha hq (max R (L + D))
  obtain ⟨z, hz, hza, he, hdist⟩ := hnear z₀ hb ((le_max_left _ _).trans hnorm.le)
  refine ⟨z, hz, hza, he, ?_⟩
  have hlarge : L + D < ‖z₀‖ := (le_max_right _ _).trans_lt hnorm
  have ht : ‖z₀‖ ≤ ‖z‖ + ‖z - z₀‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le z (z - z₀)
  linarith only [hlarge, ht, hdist]

/-- The actual spherical TM determinant has nonzero zeros of arbitrarily
large modulus in each degree, with no algebraicity assumption on n. -/
theorem unbounded_tm_zeros (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l n z = 0 ∧ L < ‖z‖ := by
  have hA : (plusPolynomial l n).eval 0 ≠ 0 := by
    rw [plusPolynomial_zero]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) I_ne_zero) (sub_ne_zero.mpr hp)
  have hB : (minusPolynomial l n).eval 0 ≠ 0 := by
    rw [minusPolynomial_zero]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) I_ne_zero)
      (by simpa using sub_ne_zero.mpr hm)
  have ha : 2 * I * n ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn
  obtain ⟨z, hz, hza, he, hlarge⟩ := unbounded_exponential_polynomial_roots
    (plusPolynomial l n) (minusPolynomial l n) (2 * I * n) hA hB ha L
  rw [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv] at hza
  rw [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz),
    minusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv] at he
  exact ⟨z, hz, (tmDet_zero_iff_exp l n z hza).mpr he, hlarge⟩

/-- Fixed-degree simplicity at arbitrarily large modulus follows from
the actual construction and the proved finite exceptional set. It does
not assert separation from every other degree. -/
theorem unbounded_simple_tm_zeros (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l n z = 0 ∧ deriv (tmDet l n) z ≠ 0 ∧ L < ‖z‖ := by
  obtain ⟨b, hb⟩ := Set.exists_upper_bound_image
    {z : ℂ | z ≠ 0 ∧ tmDet l n z = 0 ∧ deriv (tmDet l n) z = 0}
    norm (finite_multiple_zeros l n hn hp hm)
  obtain ⟨z, hz, he, hlarge⟩ := unbounded_tm_zeros l n hn hp hm (max L ‖b‖)
  refine ⟨z, hz, he, ?_, (le_max_left _ _).trans_lt hlarge⟩
  intro hd
  have hle := hb z ⟨hz, he, hd⟩
  exact (not_le_of_gt ((le_max_right _ _).trans_lt hlarge)) hle

/-- Actual poles can avoid any prescribed finite set of points, in
addition to being simple within their own degree. -/
theorem simple_tm_zero_avoiding_finite (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (S : Set ℂ) (hS : S.Finite) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l n z = 0 ∧ deriv (tmDet l n) z ≠ 0 ∧
      z ∉ S ∧ L < ‖z‖ := by
  obtain ⟨b, hb⟩ := Set.exists_upper_bound_image S norm hS
  obtain ⟨z, hz, he, hd, hlarge⟩ := unbounded_simple_tm_zeros l n hn hp hm (max L ‖b‖)
  refine ⟨z, hz, he, hd, ?_, (le_max_left _ _).trans_lt hlarge⟩
  intro hs
  exact (not_le_of_gt ((le_max_right _ _).trans_lt hlarge)) (hb z hs)

end OQ14.ModalExistence

#print axioms OQ14.ModalExistence.inverse_fixed_point
#print axioms OQ14.ModalExistence.polynomial_contDiff
#print axioms OQ14.ModalExistence.exponential_polynomial_nearby
#print axioms OQ14.ModalExistence.unbounded_constant_exponential_roots
#print axioms OQ14.ModalExistence.unbounded_exponential_polynomial_roots
#print axioms OQ14.ModalExistence.unbounded_tm_zeros
#print axioms OQ14.ModalExistence.unbounded_simple_tm_zeros
#print axioms OQ14.ModalExistence.simple_tm_zero_avoiding_finite

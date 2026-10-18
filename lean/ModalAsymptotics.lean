import ModalExistence

/-!
# Actual small-displacement modal roots

The local contraction is sharpened to an arbitrarily small displacement.
No asymptotic root location or physical operator pole is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalAsymptotics

open Complex Metric Set OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.ModalRational
  OQ14.ModalExistence
open scoped NNReal

/-- The nearby roots have displacement tending to zero, not merely bounded
displacement, along any sufficiently large constant-quotient root. -/
theorem exponential_polynomial_close (A B : Polynomial ℂ) (a : ℂ)
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (ha : a ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z₀ : ℂ,
      exp (a * z₀) = -B.eval 0 / A.eval 0 → R ≤ ‖z₀‖ →
      ∃ z : ℂ, z ≠ 0 ∧ A.eval z⁻¹ ≠ 0 ∧
        exp (a * z) = -B.eval z⁻¹ / A.eval z⁻¹ ∧ ‖z - z₀‖ < ε := by
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
  have hHev : ∀ᶠ w in nhds (0 : ℂ), ‖H w‖ < ε := by
    have hnorm : ‖H 0‖ < ε := by simpa only [hH0, norm_zero] using hε
    exact hH.continuousAt.norm.tendsto.eventually (gt_mem_nhds hnorm)
  have hregion : t ∩ {w : ℂ | Q w ≠ 0 ∧ A.eval w ≠ 0 ∧ ‖H w‖ < ε} ∈
      nhds (0 : ℂ) := Filter.inter_mem ht (hQev.and (hAev.and hHev))
  obtain ⟨r, hr, hrt⟩ := nhds_basis_closedBall.mem_iff.mp hregion
  have hClip : LipschitzOnWith C H (closedBall 0 r) := hCt.mono (fun w hw => (hrt hw).1)
  refine ⟨C * r + 2 * C + 1 + r⁻¹, ?_⟩
  intro z₀ hbase hz₀
  obtain ⟨z, hz, hw, hsol, -⟩ := inverse_fixed_point H C r hr hClip hH0 z₀ hz₀
  have hwQ : Q z⁻¹ ≠ 0 := (hrt hw).2.1
  have hwA : A.eval z⁻¹ ≠ 0 := (hrt hw).2.2.1
  refine ⟨z, hz, hwA, ?_, ?_⟩
  · change exp (a * z) = Q z⁻¹
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
  · have heq : z - z₀ = H z⁻¹ := by linear_combination hsol
    rw [heq]
    exact (hrt hw).2.2.2

/-- Actual determinant zeros approach the explicit constant matching
equation in every fixed degree. -/
theorem tm_zero_close (l : ℕ) (n : ℂ)
    (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z₀ : ℂ,
      exp (2 * I * n * z₀) = -(minusPolynomial l n).eval 0 / (plusPolynomial l n).eval 0 →
      R ≤ ‖z₀‖ → ∃ z : ℂ, z ≠ 0 ∧ tmDet l n z = 0 ∧ ‖z - z₀‖ < ε := by
  have hA : (plusPolynomial l n).eval 0 ≠ 0 := by
    rw [plusPolynomial_zero]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) I_ne_zero) (sub_ne_zero.mpr hp)
  have hB : (minusPolynomial l n).eval 0 ≠ 0 := by
    rw [minusPolynomial_zero]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) I_ne_zero)
      (by simpa using sub_ne_zero.mpr hm)
  have ha : 2 * I * n ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hn
  obtain ⟨R, hR⟩ := exponential_polynomial_close
    (plusPolynomial l n) (minusPolynomial l n) (2 * I * n) hA hB ha ε hε
  refine ⟨R, ?_⟩
  intro z₀ hbase hlarge
  obtain ⟨z, hz, hza, he, hdist⟩ := hR z₀ hbase hlarge
  rw [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv] at hza
  rw [plusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz),
    minusPolynomial_eval l n z⁻¹ hn (inv_ne_zero hz), inv_inv] at he
  exact ⟨z, hz, (tmDet_zero_iff_exp l n z hza).mpr he, hdist⟩

def exponentialCenter (b : ℝ) (q : ℂ) (m : ℕ) : ℂ :=
  (log q + (m : ℂ) * (2 * Real.pi * I)) / (I * b)

theorem exponentialCenter_exp (b : ℝ) (hb : b ≠ 0) (q : ℂ) (hq : q ≠ 0) (m : ℕ) :
    exp (I * b * exponentialCenter b q m) = q := by
  unfold exponentialCenter
  rw [mul_div_cancel₀ _ (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb)),
    exp_add, exp_log hq, exp_nat_mul_two_pi_mul_I, mul_one]

theorem exponentialCenter_re (b : ℝ) (hb : b ≠ 0) (q : ℂ) (m : ℕ) :
    (exponentialCenter b q m).re = ((log q).im + (m : ℝ) * (2 * Real.pi)) / b := by
  simp only [exponentialCenter, div_re, add_re, add_im, mul_re, mul_im,
    I_re, I_im, ofReal_re, ofReal_im, natCast_re, natCast_im, zero_mul, mul_zero,
    one_mul, zero_sub, sub_zero, add_zero, zero_add, normSq_mul, normSq_I,
    normSq_ofReal, zero_div]
  field_simp
  ring

theorem exponentialCenter_im (b : ℝ) (hb : b ≠ 0) (q : ℂ) (m : ℕ) :
    (exponentialCenter b q m).im = -Real.log ‖q‖ / b := by
  simp only [exponentialCenter, div_im, add_re, add_im, mul_re, mul_im,
    I_re, I_im, ofReal_re, ofReal_im, natCast_re, natCast_im, zero_mul, mul_zero,
    one_mul, zero_sub, sub_zero, add_zero, zero_add, normSq_mul, normSq_I,
    normSq_ofReal, zero_div, log_re]
  field_simp
  ring

theorem exponentialCenter_re_unbounded (b : ℝ) (hb : 0 < b) (q : ℂ) (L : ℝ) :
    ∃ m : ℕ, L < (exponentialCenter b q m).re := by
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  obtain ⟨m, hm⟩ := exists_nat_gt ((b * L - (log q).im) / (2 * Real.pi))
  refine ⟨m, ?_⟩
  rw [exponentialCenter_re b hb.ne' q m]
  apply (lt_div_iff₀ hb).2
  have hm' := (div_lt_iff₀ hp).mp hm
  linarith only [hm']

/-- For a positive imaginary exponential rate, the actual roots approach
the horizontal line dictated by the modulus of the constant quotient. -/
theorem exponential_polynomial_strip (A B : Polynomial ℂ) (b : ℝ)
    (hA : A.eval 0 ≠ 0) (hB : B.eval 0 ≠ 0) (hb : 0 < b)
    (ε : ℝ) (hε : 0 < ε) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ A.eval z⁻¹ ≠ 0 ∧
      exp (I * b * z) = -B.eval z⁻¹ / A.eval z⁻¹ ∧ L < z.re ∧
      |z.im + Real.log ‖-B.eval 0 / A.eval 0‖ / b| < ε := by
  have ha : I * (b : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')
  obtain ⟨R, hR⟩ := exponential_polynomial_close A B (I * b) hA hB ha ε hε
  let q : ℂ := -B.eval 0 / A.eval 0
  have hq : q ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hA
  obtain ⟨m, hm⟩ := exponentialCenter_re_unbounded b hb q (max R (L + ε))
  let z₀ := exponentialCenter b q m
  have hz₀ : R ≤ ‖z₀‖ :=
    (le_max_left _ _).trans (hm.le.trans (re_le_norm z₀))
  obtain ⟨z, hz, hza, he, hdist⟩ := hR z₀ (exponentialCenter_exp b hb.ne' q hq m) hz₀
  refine ⟨z, hz, hza, he, ?_, ?_⟩
  · have hr := (abs_re_le_norm (z - z₀)).trans_lt hdist
    rw [sub_re, abs_lt] at hr
    have hbig := (le_max_right R (L + ε)).trans_lt hm
    change L + ε < z₀.re at hbig
    linarith only [hr.1, hbig]
  · have hi := (abs_im_le_norm (z - z₀)).trans_lt hdist
    rw [sub_im, show z₀.im = -Real.log ‖q‖ / b from exponentialCenter_im b hb.ne' q m] at hi
    simpa only [sub_neg_eq_add, neg_div, q] using hi

theorem tm_constant_quotient_norm (l : ℕ) (n : ℝ) (hn : 1 < n) :
    ‖-(minusPolynomial l (n : ℂ)).eval 0 / (plusPolynomial l (n : ℂ)).eval 0‖ =
      (n + 1) / (n - 1) := by
  rw [norm_div, norm_neg, minusPolynomial_zero, plusPolynomial_zero]
  simp only [norm_mul, norm_pow, norm_I, norm_neg, one_pow, one_mul]
  have hp : 0 < n + 1 := by linarith
  have hm : 0 < n - 1 := sub_pos.mpr hn
  simp only [← ofReal_one, ← ofReal_add, ← ofReal_sub, norm_real,
    Real.norm_eq_abs, abs_of_pos hp, abs_of_pos hm]

/-- At a real ordinary refractive index, actual TM zeros approach the
strictly lower horizontal line determined by dielectric reflection. -/
theorem tm_zero_strip (l : ℕ) (n : ℝ) (hn : 1 < n)
    (ε : ℝ) (hε : 0 < ε) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ L < z.re ∧
      |z.im + Real.log ((n + 1) / (n - 1)) / (2 * n)| < ε := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hn1 : (n : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hn)
  have hnm : (n : ℂ) ≠ -1 := by exact_mod_cast (show n ≠ -1 by linarith)
  have hA : (plusPolynomial l (n : ℂ)).eval 0 ≠ 0 := by
    rw [plusPolynomial_zero]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr I_ne_zero)) I_ne_zero) (sub_ne_zero.mpr hn1)
  have hB : (minusPolynomial l (n : ℂ)).eval 0 ≠ 0 := by
    rw [minusPolynomial_zero]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ I_ne_zero) I_ne_zero)
      (by simpa using sub_ne_zero.mpr hnm)
  have hb : 0 < 2 * n := by linarith
  obtain ⟨z, hz, hza, he, hlarge, hstrip⟩ := exponential_polynomial_strip
    (plusPolynomial l (n : ℂ)) (minusPolynomial l (n : ℂ)) (2 * n) hA hB hb ε hε L
  rw [tm_constant_quotient_norm l n hn] at hstrip
  rw [plusPolynomial_eval l (n : ℂ) z⁻¹ hn0 (inv_ne_zero hz), inv_inv] at hza
  rw [plusPolynomial_eval l (n : ℂ) z⁻¹ hn0 (inv_ne_zero hz),
    minusPolynomial_eval l (n : ℂ) z⁻¹ hn0 (inv_ne_zero hz), inv_inv] at he
  have he' : exp (2 * I * (n : ℂ) * z) = rationalPole l (n : ℂ) z := by
    have hr : I * ((2 * n : ℝ) : ℂ) = 2 * I * (n : ℂ) := by
      push_cast
      ring
    simpa only [hr, rationalPole] using he
  exact ⟨z, hz, (tmDet_zero_iff_exp l (n : ℂ) z hza).mpr he', hlarge, hstrip⟩

theorem tm_simple_zero_strip (l : ℕ) (n : ℝ) (hn : 1 < n)
    (ε : ℝ) (hε : 0 < ε) (L : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ deriv (tmDet l (n : ℂ)) z ≠ 0 ∧
      L < z.re ∧ |z.im + Real.log ((n + 1) / (n - 1)) / (2 * n)| < ε := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hn1 : (n : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hn)
  have hnm : (n : ℂ) ≠ -1 := by exact_mod_cast (show n ≠ -1 by linarith)
  obtain ⟨b, hb⟩ := Set.exists_upper_bound_image
    {z : ℂ | z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ deriv (tmDet l (n : ℂ)) z = 0}
    norm (finite_multiple_zeros l (n : ℂ) hn0 hn1 hnm)
  obtain ⟨z, hz, he, hlarge, hstrip⟩ := tm_zero_strip l n hn ε hε (max L ‖b‖)
  refine ⟨z, hz, he, ?_, (le_max_left _ _).trans_lt hlarge, hstrip⟩
  intro hd
  have hle := hb z ⟨hz, he, hd⟩
  have hgt : ‖b‖ < ‖z‖ := ((le_max_right _ _).trans_lt hlarge).trans_le (re_le_norm z)
  exact (not_le_of_gt hgt) hle

/-- Each fixed angular degree has actual simple determinant zeros in the
lower half-plane with an arbitrarily large positive frequency-to-decay
ratio. This is a scalar determinant conclusion, not operator identification. -/
theorem tm_high_quality_zeros (l : ℕ) (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ z : ℂ, z ≠ 0 ∧ tmDet l (n : ℂ) z = 0 ∧ deriv (tmDet l (n : ℂ)) z ≠ 0 ∧
      L < z.re ∧ z.im < 0 ∧ Q < z.re / (-2 * z.im) := by
  let c : ℝ := Real.log ((n + 1) / (n - 1)) / (2 * n)
  have hratio : 1 < (n + 1) / (n - 1) := by
    apply (lt_div_iff₀ (sub_pos.mpr hn)).2
    linarith
  have hc : 0 < c := div_pos (Real.log_pos hratio) (by linarith)
  obtain ⟨z, hz, he, hd, hlarge, hstrip⟩ := tm_simple_zero_strip l n hn
    (c / 2) (half_pos hc) (max L (3 * c * Q))
  change |z.im + c| < c / 2 at hstrip
  rw [abs_lt] at hstrip
  have hi : z.im < 0 := by linarith only [hstrip.2, hc]
  refine ⟨z, hz, he, hd, (le_max_left _ _).trans_lt hlarge, hi, ?_⟩
  apply (lt_div_iff₀ (by linarith : 0 < -2 * z.im)).2
  have hbig : 3 * c * Q < z.re := (le_max_right _ _).trans_lt hlarge
  have hprod := mul_le_mul_of_nonneg_left (show -2 * z.im ≤ 3 * c by linarith only [hstrip.1]) hQ
  nlinarith only [hprod, hbig]

end OQ14.ModalAsymptotics

#print axioms OQ14.ModalAsymptotics.exponential_polynomial_close
#print axioms OQ14.ModalAsymptotics.tm_zero_close
#print axioms OQ14.ModalAsymptotics.exponentialCenter_exp
#print axioms OQ14.ModalAsymptotics.exponentialCenter_re
#print axioms OQ14.ModalAsymptotics.exponentialCenter_im
#print axioms OQ14.ModalAsymptotics.exponentialCenter_re_unbounded
#print axioms OQ14.ModalAsymptotics.exponential_polynomial_strip
#print axioms OQ14.ModalAsymptotics.tm_constant_quotient_norm
#print axioms OQ14.ModalAsymptotics.tm_zero_strip
#print axioms OQ14.ModalAsymptotics.tm_simple_zero_strip
#print axioms OQ14.ModalAsymptotics.tm_high_quality_zeros

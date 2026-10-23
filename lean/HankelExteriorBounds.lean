import HankelCoefficientBounds
import ScalarGreenRadialBound
import RadialHighOrderTail

/-! Genuine all-degree Hankel bounds uniform throughout a fixed positive exterior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HankelExteriorBounds
open OQ14.HankelCoefficientBounds OQ14.ModalAlgebra

theorem coefficient_sum_mono (l : ℕ) (R r : ℝ) (hR : 0<R) (hr : R≤r) :
    (∑ s∈Finset.range (l+1),coefficient l s/r^s)≤
      ∑ s∈Finset.range (l+1),coefficient l s/R^s := by
  apply Finset.sum_le_sum
  intro s _
  exact div_le_div_of_nonneg_left (coefficient_pos l s).le (pow_pos hR s)
    (pow_le_pow_left₀ hR.le hr s)

theorem poly_uniform (l : ℕ) (z : ℂ) (hz : ‖z‖=1) (R r : ℝ) (hR : 0<R) (hr : R≤r) :
    ‖hankelPoly l z r‖≤coefficient l l/R^l*Real.exp R :=
  (hankelPoly_norm_sum l z hz r (hR.trans_le hr)).trans
    ((coefficient_sum_mono l R r hR hr).trans (coefficient_sum_exponential_bound l R hR))

theorem polyD_uniform (l : ℕ) (z : ℂ) (hz : ‖z‖=1) (R r : ℝ) (hR : 0<R) (hr : R≤r) :
    ‖hankelPolyD l z r‖≤((l : ℝ)/R)*(coefficient l l/R^l*Real.exp R) := by
  apply (hankelPolyD_norm_sum l z hz r (hR.trans_le hr)).trans
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg l) hR hr
  · exact (coefficient_sum_mono l R r hR hr).trans (coefficient_sum_exponential_bound l R hR)
  · exact Finset.sum_nonneg (fun s _ => div_nonneg (coefficient_pos l s).le
      (pow_nonneg (hR.trans_le hr).le s))
  · positivity

theorem xi_uniform (l : ℕ) (R r : ℝ) (hR : 0<R) (hr : R≤r) :
    ‖xi l r‖≤coefficient l l/R^l*Real.exp R := by
  simpa [xi,norm_mul,norm_pow,Complex.norm_exp,p] using poly_uniform l Complex.I (by simp) R r hR hr

theorem xiD_uniform (l : ℕ) (R r : ℝ) (hR : 0<R) (hr : R≤r) :
    ‖xiD l r‖≤(1+(l : ℝ)/R)*(coefficient l l/R^l*Real.exp R) := by
  have he : ‖xiD l r‖=‖Complex.I*p l r+pD l r‖ := by simp [xiD,norm_mul,norm_pow,Complex.norm_exp]
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_I,one_mul]
  exact (add_le_add (poly_uniform l Complex.I (by simp) R r hR hr)
    (polyD_uniform l Complex.I (by simp) R r hR hr)).trans_eq (by ring)

theorem regular_outgoing_product (l : ℕ) (B R r : ℝ) (hB : 0≤B) (hR : 0<R) (hr : R≤r) :
    RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xi l r‖≤
      Real.exp R/(2*(l : ℝ)+1)*(B/R)^l := by
  calc
    _ ≤ RiccatiSeriesCoefficients.amplitude l 0*B^l*(coefficient l l/R^l*Real.exp R) :=
      mul_le_mul_of_nonneg_left (xi_uniform l R r hR hr)
        (mul_nonneg (RiccatiSeriesCoefficients.amplitude_pos l 0).le (pow_nonneg hB l))
    _ = (RiccatiSeriesCoefficients.amplitude l 0*coefficient l l)*Real.exp R*(B/R)^l := by
      rw [div_pow]
      ring
    _ = _ := by rw [ScalarGreenRadialBound.amplitude_leading_product];ring

theorem regular_outgoing_derivative_product (l : ℕ) (B R r : ℝ) (hB : 0≤B) (hR : 0<R) (hr : R≤r) :
    RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xiD l r‖≤
      (1+(l : ℝ)/R)*(Real.exp R/(2*(l : ℝ)+1)*(B/R)^l) := by
  calc
    _ ≤ RiccatiSeriesCoefficients.amplitude l 0*B^l*((1+(l : ℝ)/R)*(coefficient l l/R^l*Real.exp R)) :=
      mul_le_mul_of_nonneg_left (xiD_uniform l R r hR hr)
        (mul_nonneg (RiccatiSeriesCoefficients.amplitude_pos l 0).le (pow_nonneg hB l))
    _ = (1+(l : ℝ)/R)*((RiccatiSeriesCoefficients.amplitude l 0*coefficient l l)*Real.exp R*(B/R)^l) := by
      rw [div_pow]
      ring
    _ = _ := by rw [ScalarGreenRadialBound.amplitude_leading_product];ring

theorem regular_outgoing_geometric (l : ℕ) (B R r : ℝ) (hB : 0≤B) (hR : 1≤R)
    (hBR : 2*B≤R) (hr : R≤r) :
    RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xi l r‖≤Real.exp R*(1/2 : ℝ)^l ∧
    RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xiD l r‖≤Real.exp R*(1/2 : ℝ)^l := by
  have hR0 : 0<R := zero_lt_one.trans_le hR
  have hden : 0<2*(l : ℝ)+1 := by positivity
  have hlR : (l : ℝ)/R≤l := div_le_self (Nat.cast_nonneg l) hR
  have hp : (B/R)^l≤(1/2 : ℝ)^l :=
    pow_le_pow_left₀ (div_nonneg hB hR0.le) ((div_le_iff₀ hR0).mpr (by linarith)) l
  have hbase : Real.exp R*(B/R)^l≤Real.exp R*(1/2 : ℝ)^l :=
    mul_le_mul_of_nonneg_left hp (Real.exp_pos R).le
  constructor
  · apply (regular_outgoing_product l B R r hB hR0 hr).trans
    apply le_trans _ hbase
    exact mul_le_mul_of_nonneg_right (div_le_self (Real.exp_pos R).le (by linarith [Nat.cast_nonneg (α := ℝ) l]))
      (pow_nonneg (div_nonneg hB hR0.le) l)
  · apply (regular_outgoing_derivative_product l B R r hB hR0 hr).trans
    apply le_trans _ hbase
    calc
      _ = ((1+(l : ℝ)/R)/(2*(l : ℝ)+1))*Real.exp R*(B/R)^l := by ring
      _ ≤ 1*Real.exp R*(B/R)^l := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (div_nonneg hB hR0.le) l)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos R).le
        exact (div_le_one hden).mpr (by linarith [Nat.cast_nonneg (α := ℝ) l])
      _ = _ := by ring

theorem polynomial_weighted_summable (k : ℕ) (B R r : ℝ) (hB : 0≤B) (hR : 1≤R)
    (hBR : 2*B≤R) (hr : R≤r) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*RiccatiSeriesCoefficients.amplitude l 0*B^l*
      (‖xi l r‖+‖xiD l r‖)) := by
  apply Summable.of_nonneg_of_le (fun l => by
      have h := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
      positivity)
    (fun l => ?_) ((RadialHighOrderTail.polynomial_geometric_summable k).mul_left (2*Real.exp R))
  have h := regular_outgoing_geometric l B R r hB hR hBR hr
  calc
    _ = (l+1 : ℝ)^k*(RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xi l r‖+
        RiccatiSeriesCoefficients.amplitude l 0*B^l*‖xiD l r‖) := by ring
    _ ≤ (l+1 : ℝ)^k*(Real.exp R*(1/2 : ℝ)^l+Real.exp R*(1/2 : ℝ)^l) :=
      mul_le_mul_of_nonneg_left (add_le_add h.1 h.2) (by positivity)
    _ = _ := by ring

end OQ14.HankelExteriorBounds

#print axioms OQ14.HankelExteriorBounds.coefficient_sum_mono
#print axioms OQ14.HankelExteriorBounds.poly_uniform
#print axioms OQ14.HankelExteriorBounds.polyD_uniform
#print axioms OQ14.HankelExteriorBounds.xi_uniform
#print axioms OQ14.HankelExteriorBounds.xiD_uniform
#print axioms OQ14.HankelExteriorBounds.regular_outgoing_product
#print axioms OQ14.HankelExteriorBounds.regular_outgoing_derivative_product
#print axioms OQ14.HankelExteriorBounds.regular_outgoing_geometric
#print axioms OQ14.HankelExteriorBounds.polynomial_weighted_summable

import PolynomialCoefficientNorm
import EquispacedProducts

/-! Actual spatial polynomial interpolation at literal separated real grid nodes. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.PolynomialGridInterpolation

open OQ14.HarmonicPolynomial OQ14.PolynomialJetBounds OQ14.PolynomialCoefficientNorm
  OQ14.EquispacedProducts

def factor (l : ℕ) (i : Fin 3) (a b : Fin (l+1)) : Poly :=
  MvPolynomial.C (node l a-node l b)⁻¹*(MvPolynomial.X i-MvPolynomial.C (node l b))

def gridBasis (l : ℕ) (i : Fin 3) (a : Fin (l+1)) : Poly :=
  ∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a, factor l i a b

theorem gridBasis_eq_aeval (l : ℕ) (i : Fin 3) (a : Fin (l+1)) :
    gridBasis l i a=Polynomial.aeval (MvPolynomial.X i : Poly)
      (Lagrange.basis Finset.univ (node l) a) := by
  simp [gridBasis,Lagrange.basis,Lagrange.basisDivisor,factor,Polynomial.aeval_C]

theorem power_interpolation (l e : ℕ) (he : e ≤ l) (i : Fin 3) :
    (MvPolynomial.X i : Poly)^e=∑ a : Fin (l+1),
      MvPolynomial.C (node l a^e)*gridBasis l i a := by
  have hnodes : Set.InjOn (node l) (Finset.univ : Finset (Fin (l+1))) :=
    (node_injective l).injOn
  have hdegree : (Polynomial.X^e : Polynomial ℝ).degree < ((Finset.univ : Finset (Fin (l+1))).card : ℕ) := by
    rw [Polynomial.degree_X_pow,Finset.card_univ,Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le he
  have h := Lagrange.eq_interpolate hnodes hdegree
  have hmap := congrArg (Polynomial.aeval (MvPolynomial.X i : Poly)) h
  simpa only [map_pow,Polynomial.aeval_X,Lagrange.interpolate,LinearMap.coe_mk,AddHom.coe_mk,
    Polynomial.eval_pow,Polynomial.eval_X,map_sum,map_mul,Polynomial.aeval_C,← gridBasis_eq_aeval] using hmap

theorem factor_norm (l : ℕ) (i : Fin 3) (a b : Fin (l+1)) :
    coefficientNorm (factor l i a b) ≤ 2*|node l a-node l b|⁻¹ := by
  have hb : coefficientNorm (MvPolynomial.X i-MvPolynomial.C (node l b)) ≤ 2 := by
    calc
      _ ≤ coefficientNorm (MvPolynomial.X i)+coefficientNorm (-MvPolynomial.C (node l b)) :=
        by simpa only [sub_eq_add_neg] using
          coefficientNorm_add (MvPolynomial.X i) (-MvPolynomial.C (node l b))
      _ = 1+|node l b| := by rw [coefficientNorm_X,coefficientNorm_neg,coefficientNorm_C,Real.norm_eq_abs]
      _ ≤ 2 := by rw [abs_of_nonneg (node_nonneg l b)]; linarith [node_lt_one l b]
  calc
    _ ≤ coefficientNorm (MvPolynomial.C (node l a-node l b)⁻¹)*
        coefficientNorm (MvPolynomial.X i-MvPolynomial.C (node l b)) := coefficientNorm_mul _ _
    _ ≤ |node l a-node l b|⁻¹*2 := by
      rw [coefficientNorm_C,norm_inv,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := mul_comm _ _

def weight (l : ℕ) (a : Fin (l+1)) : ℝ :=
  2^l*((l+1 : ℕ) : ℝ)^l/((a.val.factorial : ℝ)*((l-a.val).factorial : ℝ))

theorem weight_nonneg (l : ℕ) (a : Fin (l+1)) : 0 ≤ weight l a := by unfold weight; positivity

theorem gridBasis_norm (l : ℕ) (i : Fin 3) (a : Fin (l+1)) :
    coefficientNorm (gridBasis l i a) ≤ weight l a := by
  calc
    _ ≤ ∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a,coefficientNorm (factor l i a b) :=
      coefficientNorm_prod _ _
    _ ≤ ∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a,2*|node l a-node l b|⁻¹ :=
      Finset.prod_le_prod (fun b _ => coefficientNorm_nonneg _) (fun b _ => factor_norm l i a b)
    _ = 2^l*(∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a,|node l a-node l b|)⁻¹ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_inv_distrib]
      simp
    _ = weight l a := by rw [node_difference_product,inv_div]; unfold weight; ring

theorem reciprocal_factorials (l : ℕ) (a : Fin (l+1)) :
    1/((a.val.factorial : ℝ)*((l-a.val).factorial : ℝ))=
      (l.choose a.val : ℝ)/(l.factorial : ℝ) := by
  have h : (l.choose a.val : ℝ)*(a.val.factorial : ℝ)*((l-a.val).factorial : ℝ)=(l.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ a.isLt)
  have ha : (a.val.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a.val
  have hb : ((l-a.val).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (l-a.val)
  have hl : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  field_simp [ha,hb,hl]
  nlinarith [h]

theorem weight_sum (l : ℕ) :
    (∑ a : Fin (l+1),weight l a)=4^l*((l+1 : ℕ) : ℝ)^l/(l.factorial : ℝ) := by
  have hw (a : Fin (l+1)) : weight l a=
      (2^l*((l+1 : ℕ) : ℝ)^l/(l.factorial : ℝ))*(l.choose a.val : ℝ) := by
    dsimp only [weight]
    calc
      _ = (2^l*((l+1 : ℕ) : ℝ)^l)*(1/((a.val.factorial : ℝ)*((l-a.val).factorial : ℝ))) := by ring
      _ = _ := by rw [reciprocal_factorials]; ring
  simp_rw [hw]
  rw [← Finset.mul_sum]
  have hc : (∑ a : Fin (l+1),(l.choose a.val : ℝ))=(2 : ℝ)^l := by
    have hn : (∑ a : Fin (l+1),l.choose a.val)=2^l := by
      rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => l.choose a) (l+1),Nat.sum_range_choose]
    exact_mod_cast hn
  rw [hc]
  have hfour : (4 : ℝ)^l=2^l*2^l := by rw [← mul_pow]; norm_num
  rw [hfour]
  ring

theorem weight_sum_bound (l : ℕ) :
    (∑ a : Fin (l+1),weight l a) ≤ 4^l*Real.exp (((l+1 : ℕ) : ℝ)) := by
  rw [weight_sum]
  calc
    _ = 4^l*(((l+1 : ℕ) : ℝ)^l/(l.factorial : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (((l+1 : ℕ) : ℝ)) (by positivity) l) (by positivity)

end OQ14.PolynomialGridInterpolation

#print axioms OQ14.PolynomialGridInterpolation.gridBasis_eq_aeval
#print axioms OQ14.PolynomialGridInterpolation.power_interpolation
#print axioms OQ14.PolynomialGridInterpolation.factor_norm
#print axioms OQ14.PolynomialGridInterpolation.weight_nonneg
#print axioms OQ14.PolynomialGridInterpolation.gridBasis_norm
#print axioms OQ14.PolynomialGridInterpolation.reciprocal_factorials
#print axioms OQ14.PolynomialGridInterpolation.weight_sum
#print axioms OQ14.PolynomialGridInterpolation.weight_sum_bound

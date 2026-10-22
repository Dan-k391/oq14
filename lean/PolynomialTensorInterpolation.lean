import PolynomialGridInterpolation
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Genuine three-coordinate tensor interpolation of actual spatial polynomials. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.PolynomialTensorInterpolation

open MvPolynomial OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.PolynomialJetBounds
  OQ14.PolynomialCoefficientNorm OQ14.EquispacedProducts OQ14.PolynomialGridInterpolation

def gridPoint (l : ℕ) (a b c : Fin (l+1)) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![node l a,node l b,node l c]

def tensor (l : ℕ) (a b c : Fin (l+1)) : Poly :=
  gridBasis l 0 a*gridBasis l 1 b*gridBasis l 2 c

theorem triple_sum_product (l : ℕ) (A B C : Fin (l+1) → Poly) :
    (∑ a,A a)*(∑ b,B b)*(∑ c,C c)=∑ a,∑ b,∑ c,A a*B b*C c := by
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul,Finset.mul_sum]

theorem monomial_interpolation (l : ℕ) (d : Fin 3 →₀ ℕ) (t : ℝ)
    (hd : ∀ i,d i ≤ l) :
    monomial d t=∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),
      C (evaluate (monomial d t) (gridPoint l a b c))*tensor l a b c := by
  have hm : monomial d t=C t*((X 0 : Poly)^(d 0)*X 1^(d 1)*X 2^(d 2)) := by
    rw [monomial_eq,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [Fin.prod_univ_three]
  conv_lhs => rw [hm,power_interpolation l (d 0) (hd 0) 0,power_interpolation l (d 1) (hd 1) 1,
    power_interpolation l (d 2) (hd 2) 2,triple_sum_product]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  have heval : evaluate (monomial d t) (gridPoint l a b c)=
      t*(node l a)^(d 0)*(node l b)^(d 1)*(node l c)^(d 2) := by
    simp only [evaluate,eval_monomial]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [gridPoint,Fin.prod_univ_three,mul_assoc]
  rw [heval]
  simp only [map_mul,map_pow,tensor]
  ring

theorem polynomial_interpolation (l : ℕ) (p : Poly)
    (hp : p ∈ restrictDegree (Fin 3) ℝ l) :
    p=∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),
      C (evaluate p (gridPoint l a b c))*tensor l a b c := by
  have hdegree := (mem_restrictDegree (Fin 3) p l).mp hp
  calc
    p = ∑ d ∈ p.support,monomial d (coeff d p) := p.as_sum
    _ = ∑ d ∈ p.support,∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),
        C (evaluate (monomial d (coeff d p)) (gridPoint l a b c))*tensor l a b c := by
      apply Finset.sum_congr rfl
      intro d hd
      exact monomial_interpolation l d (coeff d p) (hdegree d hd)
    _ = ∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),∑ d ∈ p.support,
        C (evaluate (monomial d (coeff d p)) (gridPoint l a b c))*tensor l a b c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.sum_mul,← map_sum]
      congr 2
      simp only [evaluate,← map_sum,← p.as_sum]

theorem tensor_norm (l : ℕ) (a b c : Fin (l+1)) :
    coefficientNorm (tensor l a b c) ≤ weight l a*weight l b*weight l c := by
  have h01 : coefficientNorm (gridBasis l 0 a*gridBasis l 1 b) ≤ weight l a*weight l b :=
    (coefficientNorm_mul _ _).trans (mul_le_mul (gridBasis_norm l 0 a) (gridBasis_norm l 1 b)
      (coefficientNorm_nonneg _) (weight_nonneg l a))
  exact (coefficientNorm_mul _ _).trans (mul_le_mul h01 (gridBasis_norm l 2 c)
    (coefficientNorm_nonneg _) (mul_nonneg (weight_nonneg l a) (weight_nonneg l b)))

theorem coefficient_bound_of_grid (l : ℕ) (p : Poly)
    (hp : p ∈ restrictDegree (Fin 3) ℝ l) (M : ℝ) (hM : 0 ≤ M)
    (hgrid : ∀ a b c : Fin (l+1),‖evaluate p (gridPoint l a b c)‖ ≤ M) :
    coefficientNorm p ≤ M*(∑ a : Fin (l+1),weight l a)^3 := by
  calc
    _ = coefficientNorm (∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),
        C (evaluate p (gridPoint l a b c))*tensor l a b c) :=
      congrArg coefficientNorm (polynomial_interpolation l p hp)
    _ ≤ ∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),
        coefficientNorm (C (evaluate p (gridPoint l a b c))*tensor l a b c) := by
      refine (coefficientNorm_sum _ _).trans (Finset.sum_le_sum (fun a _ => ?_))
      exact (coefficientNorm_sum _ _).trans (Finset.sum_le_sum (fun b _ => coefficientNorm_sum _ _))
    _ ≤ ∑ a : Fin (l+1),∑ b : Fin (l+1),∑ c : Fin (l+1),M*(weight l a*weight l b*weight l c) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro c _
      exact (coefficientNorm_mul _ _).trans (mul_le_mul
        (by rw [coefficientNorm_C]; exact hgrid a b c) (tensor_norm l a b c)
          (coefficientNorm_nonneg _) hM)
    _ = _ := by
      have hprod : (∑ a : Fin (l+1),weight l a)^3=∑ a : Fin (l+1),∑ b : Fin (l+1),
          ∑ c : Fin (l+1),weight l a*weight l b*weight l c := by
        calc
          _ = (∑ a : Fin (l+1),weight l a)*(∑ b : Fin (l+1),weight l b)*(∑ c : Fin (l+1),weight l c) := by ring
          _ = _ := by rw [Fintype.sum_mul_sum]; simp_rw [Finset.sum_mul,Finset.mul_sum]
      rw [hprod]
      simp_rw [Finset.mul_sum]

theorem coefficient_exp_bound_of_grid (l : ℕ) (p : Poly)
    (hp : p ∈ restrictDegree (Fin 3) ℝ l) (M : ℝ) (hM : 0 ≤ M)
    (hgrid : ∀ a b c : Fin (l+1),‖evaluate p (gridPoint l a b c)‖ ≤ M) :
    coefficientNorm p ≤ M*(4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3 := by
  refine (coefficient_bound_of_grid l p hp M hM hgrid).trans ?_
  apply mul_le_mul_of_nonneg_left _ hM
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => weight_nonneg l a)) (weight_sum_bound l) _

theorem gridPoint_norm_le_two (l : ℕ) (a b c : Fin (l+1)) : ‖gridPoint l a b c‖ ≤ 2 := by
  have hs : (node l a)^2+(node l b)^2+(node l c)^2=‖gridPoint l a b c‖^2 := by
    simpa [gridPoint,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) (gridPoint l a b c)).symm
  have hsq (z : Fin (l+1)) : (node l z)^2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self (node_nonneg l z) (node_lt_one l z).le]
  nlinarith [hsq a,hsq b,hsq c,norm_nonneg (gridPoint l a b c)]

end OQ14.PolynomialTensorInterpolation

#print axioms OQ14.PolynomialTensorInterpolation.triple_sum_product
#print axioms OQ14.PolynomialTensorInterpolation.monomial_interpolation
#print axioms OQ14.PolynomialTensorInterpolation.polynomial_interpolation
#print axioms OQ14.PolynomialTensorInterpolation.tensor_norm
#print axioms OQ14.PolynomialTensorInterpolation.coefficient_bound_of_grid
#print axioms OQ14.PolynomialTensorInterpolation.coefficient_exp_bound_of_grid
#print axioms OQ14.PolynomialTensorInterpolation.gridPoint_norm_le_two

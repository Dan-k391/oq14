import PolynomialJetBounds

/-! Genuine finite coefficient norm inequalities for spatial real polynomials. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.PolynomialCoefficientNorm

open MvPolynomial OQ14.HarmonicPolynomial OQ14.PolynomialJetBounds

theorem coefficientNorm_eq_sum (p : Poly) (s : Finset (Fin 3 →₀ ℕ)) (hs : p.support ⊆ s) :
    coefficientNorm p=∑ d ∈ s, ‖coeff d p‖ := by
  unfold coefficientNorm
  apply Finset.sum_subset hs
  intro d _ hd
  have hz : coeff d p=0 := by simpa only [mem_support_iff,not_not] using hd
  rw [hz,norm_zero]

theorem coefficientNorm_zero : coefficientNorm (0 : Poly)=0 := by simp [coefficientNorm]

theorem coefficientNorm_add (p q : Poly) :
    coefficientNorm (p+q) ≤ coefficientNorm p+coefficientNorm q := by
  rw [coefficientNorm_eq_sum (p+q) (p.support ∪ q.support) (support_add),
    coefficientNorm_eq_sum p _ Finset.subset_union_left,
    coefficientNorm_eq_sum q _ Finset.subset_union_right,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun d _ => by rw [coeff_add]; exact norm_add_le _ _)

theorem coefficientNorm_neg (p : Poly) : coefficientNorm (-p)=coefficientNorm p := by
  simp [coefficientNorm]

theorem coefficientNorm_sum {ι : Type*} (s : Finset ι) (f : ι → Poly) :
    coefficientNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coefficientNorm_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (coefficientNorm_add _ _).trans (add_le_add_left ih _)

theorem coefficientNorm_monomial (d : Fin 3 →₀ ℕ) (a : ℝ) :
    coefficientNorm (monomial d a)=‖a‖ := by
  by_cases ha : a=0
  · subst a; simp [coefficientNorm]
  · simp [coefficientNorm,support_monomial,ha]

theorem coefficientNorm_C (a : ℝ) : coefficientNorm (C a : Poly)=‖a‖ :=
  coefficientNorm_monomial 0 a

theorem coefficientNorm_one : coefficientNorm (1 : Poly)=1 := by
  simpa using coefficientNorm_C 1

theorem coefficientNorm_X (i : Fin 3) : coefficientNorm (X i : Poly)=1 := by
  simpa only [X,norm_one] using coefficientNorm_monomial (Finsupp.single i 1) 1

theorem coefficientNorm_mul (p q : Poly) :
    coefficientNorm (p*q) ≤ coefficientNorm p*coefficientNorm q := by
  have hmul : p*q=∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a+b) (coeff a p*coeff b q) := by
    calc
      _ = (∑ a ∈ p.support,monomial a (coeff a p))*(∑ b ∈ q.support,monomial b (coeff b q)) :=
        congrArg₂ (·*·) p.as_sum q.as_sum
      _ = _ := by
        simp only [Finset.sum_mul,Finset.mul_sum,monomial_mul]
        rw [Finset.sum_comm]
  rw [hmul]
  calc
    _ ≤ ∑ a ∈ p.support, coefficientNorm (∑ b ∈ q.support,monomial (a+b) (coeff a p*coeff b q)) :=
      coefficientNorm_sum _ _
    _ ≤ ∑ a ∈ p.support, ∑ b ∈ q.support,coefficientNorm (monomial (a+b) (coeff a p*coeff b q)) :=
      Finset.sum_le_sum (fun a _ => coefficientNorm_sum _ _)
    _ = coefficientNorm p*coefficientNorm q := by
      simp_rw [coefficientNorm_monomial,norm_mul]
      unfold coefficientNorm
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem coefficientNorm_prod {ι : Type*} (s : Finset ι) (f : ι → Poly) :
    coefficientNorm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coefficientNorm (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coefficientNorm_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (coefficientNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left ih (coefficientNorm_nonneg _))

end OQ14.PolynomialCoefficientNorm

#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_eq_sum
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_zero
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_add
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_neg
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_sum
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_monomial
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_C
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_one
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_X
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_mul
#print axioms OQ14.PolynomialCoefficientNorm.coefficientNorm_prod

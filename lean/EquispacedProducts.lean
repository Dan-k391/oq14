import PolynomialJetBounds
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Actual separated interpolation nodes and their factorial denominator products. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.EquispacedProducts

def node (l : ℕ) (i : Fin (l+1)) : ℝ := (i : ℕ)/(l+1 : ℕ)

theorem node_injective (l : ℕ) : Function.Injective (node l) := by
  intro i j h
  have hd : ((l+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hij : ((i : ℕ) : ℝ)=((j : ℕ) : ℝ) := (div_left_inj' hd).mp h
  apply Fin.ext
  exact_mod_cast hij

theorem node_nonneg (l : ℕ) (i : Fin (l+1)) : 0 ≤ node l i := by unfold node; positivity

theorem node_lt_one (l : ℕ) (i : Fin (l+1)) : node l i<1 := by
  unfold node
  apply (div_lt_one (by positivity)).mpr
  exact_mod_cast i.isLt

theorem descending_product (n : ℕ) :
    (∏ i : Fin n, ((n : ℝ)-((i : ℕ) : ℝ)))=(n.factorial : ℝ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (n : ℝ)-i) n,
    Finset.prod_range_natCast_sub,← Nat.descFactorial_eq_prod_range,Nat.descFactorial_self]

def distanceProduct (l : ℕ) (a : Fin (l+1)) : ℝ :=
  ∏ b : Fin (l+1), if b=a then 1 else |((a : ℕ) : ℝ)-((b : ℕ) : ℝ)|

theorem distanceProduct_factorial (l : ℕ) (a : Fin (l+1)) :
    distanceProduct l a=(a.val.factorial : ℝ)*((l-a.val).factorial : ℝ) := by
  induction l with
  | zero => fin_cases a; simp [distanceProduct]
  | succ l ih =>
    refine Fin.lastCases ?_ (fun a => ?_) a
    · unfold distanceProduct
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.castSucc_ne_last,ite_false,Fin.val_last,Fin.coe_castSucc,ite_true,mul_one,
        Nat.sub_self,Nat.factorial_zero,Nat.cast_one]
      have hge (b : Fin (l+1)) : 0 ≤ ((l+1 : ℕ) : ℝ)-((b : ℕ) : ℝ) := by
        exact sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt b.isLt))
      simp_rw [abs_of_nonneg (hge _)]
      exact descending_product (l+1)
    · unfold distanceProduct
      rw [Fin.prod_univ_castSucc]
      have hne : Fin.last (l+1) ≠ a.castSucc := (Fin.castSucc_ne_last a).symm
      simp only [Fin.castSucc_inj,Fin.coe_castSucc,hne,ite_false,Fin.val_last]
      rw [show (∏ b : Fin (l+1), if b=a then 1 else |((a : ℕ) : ℝ)-((b : ℕ) : ℝ)|)=
        (a.val.factorial : ℝ)*((l-a.val).factorial : ℝ) from ih a]
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt a.isLt)))]
      have hn : l+1-a.val=(l-a.val)+1 := by omega
      rw [hn,Nat.factorial_succ]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (by omega : a.val ≤ l)]
      ring

theorem distanceProduct_eq_erase (l : ℕ) (a : Fin (l+1)) :
    distanceProduct l a=∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a,
      |((a : ℕ) : ℝ)-((b : ℕ) : ℝ)| := by
  unfold distanceProduct
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  simp only [if_pos rfl,ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro b hb
  rw [if_neg (Finset.mem_erase.mp hb).1]

theorem node_difference_product (l : ℕ) (a : Fin (l+1)) :
    (∏ b ∈ (Finset.univ : Finset (Fin (l+1))).erase a, |node l a-node l b|)=
      (a.val.factorial : ℝ)*((l-a.val).factorial : ℝ)/((l+1 : ℕ) : ℝ)^l := by
  have hdpos : 0 < ((l+1 : ℕ) : ℝ) := by positivity
  have hdiff (b : Fin (l+1)) : |node l a-node l b|=
      |((a : ℕ) : ℝ)-((b : ℕ) : ℝ)|/((l+1 : ℕ) : ℝ) := by
    unfold node
    rw [← sub_div,abs_div,abs_of_pos hdpos]
  simp_rw [hdiff]
  rw [Finset.prod_div_distrib,Finset.prod_const]
  have hcard : ((Finset.univ : Finset (Fin (l+1))).erase a).card=l := by simp
  rw [hcard,← distanceProduct_eq_erase,distanceProduct_factorial]

end OQ14.EquispacedProducts

#print axioms OQ14.EquispacedProducts.node_injective
#print axioms OQ14.EquispacedProducts.node_nonneg
#print axioms OQ14.EquispacedProducts.node_lt_one
#print axioms OQ14.EquispacedProducts.descending_product
#print axioms OQ14.EquispacedProducts.distanceProduct_factorial
#print axioms OQ14.EquispacedProducts.distanceProduct_eq_erase
#print axioms OQ14.EquispacedProducts.node_difference_product

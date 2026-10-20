import LayeredInclusionCells
import MaterialMaxwell

/-! # Literal finite indicator-sum susceptibilities for inclusion devices -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace OQ14.LayeredInclusionCoefficient

open MeasureTheory Filter Metric Set OQ14.Maxwell
open OQ14.LayeredInclusionCells
open scoped Topology

theorem inclusion_norm_lt {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (i : ι) (x : Space) (hx : x ∈ ball (center i) (radius i)) : ‖x‖ < r 0 := by
  have ht := norm_add_le (x-center i) (center i)
  rw [sub_add_cancel,← dist_eq_norm] at ht
  have hd : dist x (center i) < radius i := hx
  linarith [hcore i]

theorem radial_norm_gt_zero {n : ℕ} (r : Fin (n+1) → ℝ) (j : Fin (n+2))
    (hj : j ≠ 0) (x : Space) (hx : x ∈ FiniteRadialPartition.cell r j) : r 0 < ‖x‖ := by
  have hjval : j.val ≠ 0 := fun h => hj (Fin.ext h)
  exact hx.1 0 (by change (0 : ℕ) < j.val; omega)

theorem radial_index_unique {n : ℕ} (r : Fin (n+1) → ℝ) (i j : Fin (n+2))
    (x : Space) (hi : x ∈ FiniteRadialPartition.cell r i)
    (hj : x ∈ FiniteRadialPartition.cell r j) : i = j := by
  apply le_antisymm
  · by_contra hle
    have hji : j.val < i.val := by change ¬ i.val ≤ j.val at hle; omega
    let cut : Fin (n+1) := ⟨j.val,by omega⟩
    have hlow := hi.1 cut hji
    have hhigh := hj.2 cut le_rfl
    exact (not_lt_of_gt hhigh) hlow
  · by_contra hle
    have hij : i.val < j.val := by change ¬ j.val ≤ i.val at hle; omega
    let cut : Fin (n+1) := ⟨i.val,by omega⟩
    have hlow := hj.1 cut hij
    have hhigh := hi.2 cut le_rfl
    exact (not_lt_of_gt hhigh) hlow

theorem inclusion_not_radial {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (i : ι) (j : Fin (n+2)) (x : Space) (hi : x ∈ ball (center i) (radius i)) :
    x ∉ cell center radius r (.inr j) := by
  intro hj
  by_cases hj0 : j = 0
  · subst j
    rw [cell_radial_zero] at hj
    exact (not_lt_of_gt (hj.2 i)) hi
  · rw [cell_radial_ne_zero center radius r j hj0] at hj
    exact (not_lt_of_gt (radial_norm_gt_zero r j hj0 x hj))
      (inclusion_norm_lt center radius r hcore i x hi)

theorem cell_index_unique {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (i j : ι ⊕ Fin (n+2)) (x : Space) (hi : x ∈ cell center radius r i)
    (hj : x ∈ cell center radius r j) : i = j := by
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · exact congrArg Sum.inl hij
    · have ht := dist_triangle (center i) x (center j)
      rw [dist_comm (center i) x] at ht
      have hs := hsep i j hij
      have hi' : dist x (center i) < radius i := hi
      have hj' : dist x (center j) < radius j := hj
      exfalso
      linarith
  · exact False.elim (inclusion_not_radial center radius r hcore i j x hi hj)
  · exact False.elim (inclusion_not_radial center radius r hcore j i x hj hi)
  · apply congrArg Sum.inr
    by_cases hi0 : i = 0
    · by_cases hj0 : j = 0
      · exact hi0.trans hj0.symm
      · subst i
        rw [cell_radial_zero] at hi
        rw [cell_radial_ne_zero center radius r j hj0] at hj
        have hlow := radial_norm_gt_zero r j hj0 x hj
        have hhigh : ‖x‖ < r 0 := mem_ball_zero_iff.mp hi.1
        exact False.elim ((not_lt_of_gt hhigh) hlow)
    · by_cases hj0 : j = 0
      · subst j
        rw [cell_radial_zero] at hj
        rw [cell_radial_ne_zero center radius r i hi0] at hi
        have hlow := radial_norm_gt_zero r i hi0 x hi
        have hhigh : ‖x‖ < r 0 := mem_ball_zero_iff.mp hj.1
        exact False.elim ((not_lt_of_gt hhigh) hlow)
      · rw [cell_radial_ne_zero center radius r i hi0] at hi
        rw [cell_radial_ne_zero center radius r j hj0] at hj
        exact radial_index_unique r i j x hi hj

theorem cells_pairwise_disjoint {ι : Type*} {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) :
    Pairwise (fun i j => Disjoint (cell center radius r i) (cell center radius r j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact hij (cell_index_unique center radius r hcore hsep i j x hi hj)

def susceptibility {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (χ : ι ⊕ Fin (n+2) → ℝ) (x : Space) : ℝ :=
  ∑ i, (cell center radius r i).indicator (fun _ => χ i) x

theorem susceptibility_measurable {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (χ : ι ⊕ Fin (n+2) → ℝ) : Measurable (susceptibility center radius r χ) := by
  unfold susceptibility
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator
    (cell_open center radius r hm i).measurableSet)

theorem susceptibility_on_cell {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (χ : ι ⊕ Fin (n+2) → ℝ) (i : ι ⊕ Fin (n+2)) (x : Space)
    (hx : x ∈ cell center radius r i) : susceptibility center radius r χ x = χ i := by
  classical
  unfold susceptibility
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    apply Set.indicator_of_not_mem
    intro hj
    exact hji (cell_index_unique center radius r hcore hsep j i x hj hx)
  · simp

theorem susceptibility_nonnegative {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ) (χ : ι ⊕ Fin (n+2) → ℝ)
    (hχ : ∀ i, 0 ≤ χ i) (x : Space) : 0 ≤ susceptibility center radius r χ x := by
  apply Finset.sum_nonneg
  intro i _
  exact Set.indicator_nonneg (fun _ _ => hχ i) x

theorem susceptibility_le_bound {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space)
    (radius : ι → ℝ) (r : Fin (n+1) → ℝ)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (χ : ι ⊕ Fin (n+2) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hχM : ∀ i, χ i ≤ M)
    (x : Space) : susceptibility center radius r χ x ≤ M := by
  classical
  by_cases hx : ∃ i, x ∈ cell center radius r i
  · obtain ⟨i,hi⟩ := hx
    rw [susceptibility_on_cell center radius r hcore hsep χ i x hi]
    exact hχM i
  · have hi : ∀ i, x ∉ cell center radius r i := fun i hi => hx ⟨i,hi⟩
    simpa only [susceptibility,Set.indicator_of_not_mem (hi _),Finset.sum_const_zero] using hM

def coefficient {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (χ : ι ⊕ Fin (n+2) → ℝ) (hχ : ∀ i, 0 ≤ χ i)
    (M : ℝ) (hM : 0 ≤ M) (hχM : ∀ i, χ i ≤ M) : StaticCoefficient.Coefficient where
  value := fun ξ => susceptibility center radius r χ (VectorFourier.coordinateMap.symm ξ)
  bound := M
  measurable := (susceptibility_measurable center radius r hm χ).comp
    VectorFourier.coordinateMap.symm.measurable
  nonnegative := fun ξ => susceptibility_nonnegative center radius r χ hχ (VectorFourier.coordinateMap.symm ξ)
  bounded := fun ξ => susceptibility_le_bound center radius r hcore hsep χ M hM hχM
    (VectorFourier.coordinateMap.symm ξ)

section Coefficient

variable {ι : Type*} [Fintype ι] {n : ℕ} (center : ι → Space) (radius : ι → ℝ)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (χ : ι ⊕ Fin (n+2) → ℝ) (hχ : ∀ i, 0 ≤ χ i)
    (M : ℝ) (hM : 0 ≤ M) (hχM : ∀ i, χ i ≤ M)

theorem coefficient_value (x : Space) :
    (coefficient center radius r hm hcore hsep χ hχ M hM hχM).value
      (VectorFourier.coordinateMap x) = susceptibility center radius r χ x := by
  simp only [coefficient,VectorFourier.coordinateMap.symm_apply_apply]

theorem coefficient_bound :
    (coefficient center radius r hm hcore hsep χ hχ M hM hχM).bound = M := rfl

theorem coefficient_on_cell (i : ι ⊕ Fin (n+2)) (x : Space)
    (hx : x ∈ cell center radius r i) :
    (coefficient center radius r hm hcore hsep χ hχ M hM hχM).value
      (VectorFourier.coordinateMap x) = χ i := by
  rw [coefficient_value]
  exact susceptibility_on_cell center radius r hcore hsep χ i x hx

theorem dielectric_on_cell (i : ι ⊕ Fin (n+2)) (x : Space)
    (hx : x ∈ cell center radius r i) :
    MaterialMaxwell.dielectric (coefficient center radius r hm hcore hsep χ hχ M hM hχM) x =
      1+χ i := by
  unfold MaterialMaxwell.dielectric
  rw [coefficient_on_cell center radius r hm hcore hsep χ hχ M hM hχM i x hx]

theorem dielectric_on_cell_ae (i : ι ⊕ Fin (n+2)) :
    ∀ᵐ x : Space, x ∈ cell center radius r i →
      MaterialMaxwell.dielectric (coefficient center radius r hm hcore hsep χ hχ M hM hχM) x =
        1+χ i :=
  Eventually.of_forall (fun x hx => dielectric_on_cell center radius r hm hcore hsep χ hχ M hM hχM i x hx)

theorem coefficient_zero_outside (hχext : χ (.inr (Fin.last (n+1))) = 0)
    (x : Space) (hx : x ∉ closedBall 0 (r (Fin.last n))) :
    (coefficient center radius r hm hcore hsep χ hχ M hM hχM).value
      (VectorFourier.coordinateMap x) = 0 := by
  have hx' : r (Fin.last n) < ‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  have hcell : x ∈ cell center radius r (.inr (Fin.last (n+1))) := by
    rw [cell_radial_ne_zero center radius r (Fin.last (n+1)) (Fin.ne_of_val_ne (by simp)),
      FiniteRadialPartition.cell_last r hm]
    exact hx'
  rw [coefficient_on_cell center radius r hm hcore hsep χ hχ M hM hχM _ x hcell,hχext]

end Coefficient

theorem dielectric_values_positive {ι : Type*} {n : ℕ} (χ : ι ⊕ Fin (n+2) → ℝ)
    (hχ : ∀ i, 0 ≤ χ i) (i : ι ⊕ Fin (n+2)) : 0 < 1+χ i := by
  linarith [hχ i]

end OQ14.LayeredInclusionCoefficient

#print axioms OQ14.LayeredInclusionCoefficient.inclusion_norm_lt
#print axioms OQ14.LayeredInclusionCoefficient.radial_norm_gt_zero
#print axioms OQ14.LayeredInclusionCoefficient.radial_index_unique
#print axioms OQ14.LayeredInclusionCoefficient.inclusion_not_radial
#print axioms OQ14.LayeredInclusionCoefficient.cell_index_unique
#print axioms OQ14.LayeredInclusionCoefficient.cells_pairwise_disjoint
#print axioms OQ14.LayeredInclusionCoefficient.susceptibility_measurable
#print axioms OQ14.LayeredInclusionCoefficient.susceptibility_on_cell
#print axioms OQ14.LayeredInclusionCoefficient.susceptibility_nonnegative
#print axioms OQ14.LayeredInclusionCoefficient.susceptibility_le_bound
#print axioms OQ14.LayeredInclusionCoefficient.coefficient
#print axioms OQ14.LayeredInclusionCoefficient.coefficient_value
#print axioms OQ14.LayeredInclusionCoefficient.coefficient_bound
#print axioms OQ14.LayeredInclusionCoefficient.coefficient_on_cell
#print axioms OQ14.LayeredInclusionCoefficient.dielectric_on_cell
#print axioms OQ14.LayeredInclusionCoefficient.dielectric_on_cell_ae
#print axioms OQ14.LayeredInclusionCoefficient.coefficient_zero_outside
#print axioms OQ14.LayeredInclusionCoefficient.dielectric_values_positive

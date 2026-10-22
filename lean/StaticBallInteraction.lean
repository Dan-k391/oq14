import StaticBallCentered

/-! # Actual static interaction between separated constant-ball sources -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallInteraction

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology BigOperators

theorem newton_exterior_bound (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, R < ‖x-c‖ →
      ‖NewtonL2.newtonOperator (StaticBallCentered.source c R P) (VectorFourier.coordinateMap x) i‖ ≤
        ((4/3 : ℝ)*(R^3/‖x-c‖^3))*(∑ j : Fin 3, ‖P j‖) := by
  rw [StaticBallCentered.newton_source c R hR P]
  filter_upwards [StaticBallCentered.response_ae c R hR P i] with x hx hout
  have hn : x-c ≠ 0 := norm_ne_zero_iff.mp (hR.trans hout).ne'
  rw [hx]
  calc
    _ ≤ ∑ j : Fin 3, ‖P j * StaticBallHessian.hessian R i j (x-c)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖P j‖*((4/3 : ℝ)*(R^3/‖x-c‖^3)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, StaticBallHessian.hessian, if_neg (not_le.mpr hout)]
      exact mul_le_mul_of_nonneg_left (StaticBallL2.exterior_norm_bound R hR i j (x-c) hn)
        (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem newton_away_bound (c : Space) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ : 0 < δ)
    (hgap : R < δ) (P : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, δ ≤ ‖x-c‖ →
      ‖NewtonL2.newtonOperator (StaticBallCentered.source c R P) (VectorFourier.coordinateMap x) i‖ ≤
        ((4/3 : ℝ)*(R^3/δ^3))*(∑ j : Fin 3, ‖P j‖) := by
  filter_upwards [newton_exterior_bound c R hR P i] with x hx hdist
  apply (hx (hgap.trans_le hdist)).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun j _ => norm_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4/3)
  exact div_le_div_of_nonneg_left (pow_nonneg hR.le _) (by positivity)
    (pow_le_pow_left₀ hδ.le hdist 3)

theorem separated_distance (p q x : Space) (r δ : ℝ)
    (hr : r ≤ δ/2) (hpq : δ ≤ dist p q) (hx : x ∈ ball p r) :
    δ/2 ≤ ‖x-q‖ := by
  have ht := dist_triangle p x q
  have hh : dist p x < r := by simpa only [mem_ball, dist_comm] using hx
  rw [dist_eq_norm x q] at ht
  linarith

theorem finite_sum_ae {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ScalarL2) :
    (fun x => (∑ j ∈ s, F j : ScalarL2) x) =ᵐ[volume] fun x => ∑ j ∈ s, F j x := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℂ 2 (volume : Measure Space))
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (F j) (∑ k ∈ s, F k), ih] with x hx hs
    exact hx.trans (congrArg (fun z => F j x+z) hs)

def crossSource {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (i : ι) : VectorL2 :=
  ∑ j ∈ Finset.univ.erase i, StaticBallCentered.source (p j) (r j) (P j)

theorem finite_cross_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (i : ι)
    (δ : ℝ) (hδ : 0 < δ) (hr : ∀ j, 0 < r j) (hsmall : ∀ j, r j ≤ δ/4)
    (hsep : ∀ j, j ≠ i → δ ≤ dist (p i) (p j)) (m : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (p i) (r i) →
      ‖NewtonL2.newtonOperator (crossSource p r P i) (VectorFourier.coordinateMap x) m‖ ≤
        ∑ j ∈ Finset.univ.erase i, ((4/3 : ℝ)*((r j)^3/(δ/2)^3))*(∑ k : Fin 3, ‖P j k‖) := by
  have he : NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (crossSource p r P i)) m =
      ∑ j ∈ Finset.univ.erase i, NewtonL2.physicalCoordinate
        (NewtonL2.newtonOperator (StaticBallCentered.source (p j) (r j) (P j))) m := by
    simp only [crossSource, map_sum, NewtonL2.physicalCoordinate]
  have hc : ∀ᵐ x : Space, ∀ j : ι,
      NewtonL2.physicalCoordinate
        (NewtonL2.newtonOperator (StaticBallCentered.source (p j) (r j) (P j))) m x =
        NewtonL2.newtonOperator (StaticBallCentered.source (p j) (r j) (P j))
          (VectorFourier.coordinateMap x) m :=
    ae_all_iff.mpr (fun j => NewtonL2.physicalCoordinate_ae _ m)
  have hb : ∀ᵐ x : Space, ∀ j : ι,
      δ/2 ≤ ‖x-p j‖ →
        ‖NewtonL2.newtonOperator (StaticBallCentered.source (p j) (r j) (P j))
          (VectorFourier.coordinateMap x) m‖ ≤
          ((4/3 : ℝ)*((r j)^3/(δ/2)^3))*(∑ k : Fin 3, ‖P j k‖) := by
    apply ae_all_iff.mpr
    intro j
    exact newton_away_bound (p j) (r j) (hr j) (δ/2) (by positivity)
      (by linarith [hsmall j]) (P j) m
  filter_upwards [NewtonL2.physicalCoordinate_ae
    (NewtonL2.newtonOperator (crossSource p r P i)) m,
    finite_sum_ae (Finset.univ.erase i) (fun j => NewtonL2.physicalCoordinate
      (NewtonL2.newtonOperator (StaticBallCentered.source (p j) (r j) (P j))) m), hc, hb]
    with x hx hs hc hb hball
  rw [← hx, he, hs]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [hc j]
  exact hb j (separated_distance (p i) (p j) x (r i) δ
    (by linarith [hsmall i]) (hsep j (Finset.mem_erase.mp hj).1) hball)

end OQ14.StaticBallInteraction

#print axioms OQ14.StaticBallInteraction.newton_exterior_bound
#print axioms OQ14.StaticBallInteraction.newton_away_bound
#print axioms OQ14.StaticBallInteraction.separated_distance
#print axioms OQ14.StaticBallInteraction.finite_sum_ae
#print axioms OQ14.StaticBallInteraction.finite_cross_bound

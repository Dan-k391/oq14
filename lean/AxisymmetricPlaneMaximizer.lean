import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

/-! A maximizer of an axisymmetric function over a closed ball centred in the plane `x 1 = 0`
can be moved into that plane without leaving the ball or changing the value. Pure geometry. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.AxisymmetricPlaneMaximizer
open Metric

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- Axisymmetry about the third axis: `F` depends on `x` only through `x 0 ^ 2 + x 1 ^ 2` and `x 2`. -/
def Axisymmetric (F : Space → ℝ) : Prop :=
  ∀ x y : Space,x 0^2+x 1^2=y 0^2+y 1^2 → x 2=y 2 → F x=F y

/-- Fold `x` into the half-plane `{x 1 = 0}` on the side of the first coordinate of `p`. -/
def fold (p x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![(if 0≤p 0 then 1 else -1)*Real.sqrt (x 0^2+x 1^2),0,x 2]

theorem fold_one (p x : Space) : fold p x 1=0 := by
  simp [fold]

theorem fold_two (p x : Space) : fold p x 2=x 2 := by
  simp [fold]

theorem fold_zero (p x : Space) :
    fold p x 0=(if 0≤p 0 then 1 else -1)*Real.sqrt (x 0^2+x 1^2) := by
  simp [fold]

theorem fold_radius (p x : Space) : fold p x 0^2+fold p x 1^2=x 0^2+x 1^2 := by
  rw [fold_zero,fold_one,mul_pow,Real.sq_sqrt (by positivity)]
  split_ifs <;> ring

theorem fold_dist_le (p x : Space) (hp : p 1=0) : dist (fold p x) p ≤ dist x p := by
  rw [EuclideanSpace.dist_eq,EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three,Real.dist_eq,sq_abs,fold_one,fold_two,hp,fold_zero]
  have hs : Real.sqrt (x 0^2+x 1^2)^2=x 0^2+x 1^2 := Real.sq_sqrt (by positivity)
  have hs0 : 0≤Real.sqrt (x 0^2+x 1^2) := Real.sqrt_nonneg _
  have hx0 : |x 0|≤Real.sqrt (x 0^2+x 1^2) := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (x 1)]
  have key : x 0*p 0 ≤ |p 0| * Real.sqrt (x 0^2+x 1^2) := by
    calc x 0*p 0 ≤ |x 0*p 0| := le_abs_self _
      _ = |x 0| * |p 0| := abs_mul _ _
      _ ≤ Real.sqrt (x 0^2+x 1^2) * |p 0| := mul_le_mul_of_nonneg_right hx0 (abs_nonneg _)
      _ = _ := mul_comm _ _
  by_cases h0 : 0≤p 0
  · rw [abs_of_nonneg h0] at key
    simp only [if_pos h0,one_mul]
    nlinarith [hs]
  · rw [abs_of_neg (not_le.mp h0)] at key
    simp only [if_neg h0]
    nlinarith [hs]

theorem exists_maximizer_in_plane (F : Space → ℝ) (hF : Axisymmetric F) (p : Space) (hp : p 1=0)
    (ε : ℝ) (x : Space) (hx : x∈closedBall p ε) (hmax : ∀ y∈closedBall p ε,F y ≤ F x) :
    ∃ x' : Space,x' 1=0 ∧ x'∈closedBall p ε ∧ F x'=F x ∧ ∀ y∈closedBall p ε,F y ≤ F x' := by
  have hF' : F (fold p x)=F x := hF _ _ (fold_radius p x) (fold_two p x)
  have hmem : fold p x∈closedBall p ε := by
    rw [mem_closedBall] at hx ⊢
    exact (fold_dist_le p x hp).trans hx
  exact ⟨fold p x,fold_one p x,hmem,hF',fun y hy => hF'.symm ▸ hmax y hy⟩

theorem exists_plane_maximizer (F : Space → ℝ) (hF : Axisymmetric F) (hc : Continuous F) (p : Space)
    (hp : p 1=0) (ε : ℝ) (hε : 0≤ε) :
    ∃ x' : Space,x' 1=0 ∧ x'∈closedBall p ε ∧ ∀ y∈closedBall p ε,F y ≤ F x' := by
  obtain ⟨x,hx,hxmax⟩ := (isCompact_closedBall p ε).exists_isMaxOn
    ⟨p,mem_closedBall_self hε⟩ hc.continuousOn
  obtain ⟨x',h1,h2,_,h4⟩ := exists_maximizer_in_plane F hF p hp ε x hx (fun y hy => hxmax hy)
  exact ⟨x',h1,h2,h4⟩

end OQ14.AxisymmetricPlaneMaximizer
#print axioms OQ14.AxisymmetricPlaneMaximizer.fold_one
#print axioms OQ14.AxisymmetricPlaneMaximizer.fold_two
#print axioms OQ14.AxisymmetricPlaneMaximizer.fold_zero
#print axioms OQ14.AxisymmetricPlaneMaximizer.fold_radius
#print axioms OQ14.AxisymmetricPlaneMaximizer.fold_dist_le
#print axioms OQ14.AxisymmetricPlaneMaximizer.exists_maximizer_in_plane
#print axioms OQ14.AxisymmetricPlaneMaximizer.exists_plane_maximizer

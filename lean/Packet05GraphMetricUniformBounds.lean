import Packet05GraphMetricCompact

/-! Uniform matrix coefficient bounds are extracted from the nine compact
metric entries, using a single chart-dependent constant. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05GraphMetricUniformBounds
open OQ14.Maxwell OQ14.WeakCurl OQ14.Packet05GraphMetricCompact
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem metric_uniform_bounds (g : Plane → ℝ) (hg : ContDiff ℝ 4 g)
    (χ : ContDiffBump (0 : Space)) :
    ∃ a b : ℝ,
      (∀ i j x, ‖(metricTest g hg χ i j).function x‖ ≤ a) ∧
      (∀ i j l x, ‖dcoord (metricTest g hg χ i j).function x l‖ ≤ b) := by
  classical
  have ha (i j : Fin 3) := (metric_test_bounds g hg χ i j 0).1
  have hb (i j l : Fin 3) := (metric_test_bounds g hg χ i j l).2
  choose A hA using ha
  choose B hB using hb
  let a : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, max (A i j) 0
  let b : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, max (B i j l) 0
  refine ⟨a,b,?_,?_⟩
  · intro i j x
    have hi : (∑ k : Fin 3, max (A i k) 0) ≤ a :=
      Finset.single_le_sum (fun m _ => Finset.sum_nonneg (fun k _ => le_max_right _ _)) (Finset.mem_univ i)
    have hj : max (A i j) 0 ≤ ∑ k : Fin 3, max (A i k) 0 :=
      Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ j)
    exact (hA i j x).trans ((le_max_left _ _).trans (hj.trans hi))
  · intro i j l x
    have hi : (∑ q : Fin 3, ∑ r : Fin 3, max (B i q r) 0) ≤ b :=
      Finset.single_le_sum (fun m _ => Finset.sum_nonneg (fun q _ =>
        Finset.sum_nonneg (fun r _ => le_max_right _ _))) (Finset.mem_univ i)
    have hj : (∑ r : Fin 3, max (B i j r) 0) ≤ ∑ q : Fin 3, ∑ r : Fin 3, max (B i q r) 0 :=
      Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun r _ => le_max_right _ _)) (Finset.mem_univ j)
    have hl : max (B i j l) 0 ≤ ∑ r : Fin 3, max (B i j r) 0 :=
      Finset.single_le_sum (fun r _ => le_max_right _ _) (Finset.mem_univ l)
    exact (hB i j l x).trans ((le_max_left _ _).trans (hl.trans (hj.trans hi)))

end OQ14.Packet05GraphMetricUniformBounds
#print axioms OQ14.Packet05GraphMetricUniformBounds.metric_uniform_bounds

import Packet05CompactGraphBounds

/-! Every actual local C³ graph admits a globally compact C³ extension that
agrees on a nonempty open disk around the chart point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ActualGraphExtension
open Set Metric OQ14.ConicalSmoothJunction OQ14.Packet05GraphCompactExtension
open scoped Topology

theorem extend_actual_graph (V : Set Plane) (hV : IsOpen V) (p : Plane) (hp : p ∈ V)
    (g : Plane → ℝ) (hg : ContDiffOn ℝ 3 g V) :
    ∃ r : ℝ, 0 < r ∧ ∃ G : Plane → ℝ,
      ContDiff ℝ 3 G ∧ HasCompactSupport G ∧
      (∀ x ∈ ball p r, G x = g x) ∧ ball p r ⊆ V := by
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV p hp
  let χ : ContDiffBump p := ⟨r/4, r/2, by positivity, by linarith⟩
  have hχV : tsupport (χ : Plane → ℝ) ⊆ V := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by dsimp [χ]; linarith)).trans hrV
  let G := extendGraph χ g
  refine ⟨r/4, by positivity, G, extend_graph_regular V hV χ g χ.contDiff hχV hg,
    extend_graph_compact χ g χ.hasCompactSupport, ?_, ?_⟩
  · intro x hx
    apply extend_graph_eq χ g (ball p (r/4)) ?_ x hx
    intro y hy
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  · exact (ball_subset_ball (by linarith : r/4 ≤ r)).trans hrV

end OQ14.Packet05ActualGraphExtension
#print axioms OQ14.Packet05ActualGraphExtension.extend_actual_graph

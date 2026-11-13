import Packet05GraphMetricRegular

/-! The actual graph metric admits a compact C³ matrix extension, with
coefficient and derivative bounds derived from its compact support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetricCompact
open MeasureTheory Metric OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalJunctionPhysical
  OQ14.Packet05GraphMetricRegular OQ14.Packet05GraphChartMatrix
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def metricTest (g : Plane → ℝ) (hg : ContDiff ℝ 4 g) (χ : ContDiffBump (0 : Maxwell.Space))
    (i j : Fin 3) : Test where
  function := fun x => (χ x : ℂ) * (metric (Packet05GraphSlope.slope g 0 x)
    (Packet05GraphSlope.slope g 1 x) i j : ℂ)
  regular := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul ((graph_metric_c3 g hg i j).of_le (by decide))
  compact := (χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right

theorem metric_test_c3 (g : Plane → ℝ) (hg : ContDiff ℝ 4 g)
    (χ : ContDiffBump (0 : Maxwell.Space)) (i j : Fin 3) :
    ContDiff ℝ 3 (metricTest g hg χ i j).function :=
  (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul (graph_metric_c3 g hg i j)

theorem metric_test_agrees (g : Plane → ℝ) (hg : ContDiff ℝ 4 g)
    (χ : ContDiffBump (0 : Maxwell.Space)) (x : Maxwell.Space)
    (hx : x ∈ closedBall 0 χ.rIn) (i j : Fin 3) :
    (metricTest g hg χ i j).function x =
      (metric (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) i j : ℂ) := by
  simp [metricTest,χ.one_of_mem_closedBall hx]

theorem metric_test_bounds (g : Plane → ℝ) (hg : ContDiff ℝ 4 g)
    (χ : ContDiffBump (0 : Maxwell.Space)) (i j l : Fin 3) :
    (∃ a : ℝ, ∀ x, ‖(metricTest g hg χ i j).function x‖ ≤ a) ∧
    (∃ b : ℝ, ∀ x, ‖dcoord (metricTest g hg χ i j).function x l‖ ≤ b) := by
  constructor
  · exact (metricTest g hg χ i j).compact.exists_bound_of_continuous
      (metricTest g hg χ i j).regular.continuous
  · exact ((metricTest g hg χ i j).compact.fderiv_apply ℝ (basis l)).exists_bound_of_continuous
      (partial_continuous (metricTest g hg χ i j).regular l)

end OQ14.Packet05GraphMetricCompact
#print axioms OQ14.Packet05GraphMetricCompact.metric_test_c3
#print axioms OQ14.Packet05GraphMetricCompact.metric_test_agrees
#print axioms OQ14.Packet05GraphMetricCompact.metric_test_bounds

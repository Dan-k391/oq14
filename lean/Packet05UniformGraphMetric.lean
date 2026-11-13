import Packet05GraphMetricComplex

/-! Uniform coercivity on a graph chart whose two slopes are bounded. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05UniformGraphMetric
open OQ14.Packet05GraphMetricComplex

theorem complex_graph_metric_uniform (a b M : ℝ) (x y z : ℂ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) :
    Complex.normSq x + Complex.normSq y + Complex.normSq z ≤
      (2+4*M^2) *
        (Complex.normSq (x-(a : ℂ)*z) + Complex.normSq (y-(b : ℂ)*z) + Complex.normSq z) := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  have ha2 : a^2 ≤ M^2 := by nlinarith [sq_abs a, abs_nonneg a]
  have hb2 : b^2 ≤ M^2 := by nlinarith [sq_abs b, abs_nonneg b]
  have he : 0 ≤ Complex.normSq (x-(a : ℂ)*z) + Complex.normSq (y-(b : ℂ)*z) + Complex.normSq z := by exact add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)
  have hc := complex_graph_metric_coercive a b x y z
  have hm : 0 ≤ ((2+4*M^2) - (2+2*a^2+2*b^2)) *
      (Complex.normSq (x-(a : ℂ)*z) + Complex.normSq (y-(b : ℂ)*z) + Complex.normSq z) :=
    mul_nonneg (by nlinarith) he
  nlinarith

end OQ14.Packet05UniformGraphMetric
#print axioms OQ14.Packet05UniformGraphMetric.complex_graph_metric_uniform

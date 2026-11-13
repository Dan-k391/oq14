import Packet05ScalarEnergyAbsorption

/-! Coercivity of the exact metric matrix of a graph-flattening chart.
The three squares are the pullback metric quadratic form. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetric

theorem graph_metric_coercive (a b x y z : ℝ) :
    x^2+y^2+z^2 ≤ (2+2*a^2+2*b^2)*((x-a*z)^2+(y-b*z)^2+z^2) := by
  have hx : x^2 ≤ 2*(x-a*z)^2 + 2*a^2*z^2 := by
    nlinarith [sq_nonneg (x-2*a*z)]
  have hy : y^2 ≤ 2*(y-b*z)^2 + 2*b^2*z^2 := by
    nlinarith [sq_nonneg (y-2*b*z)]
  have h1 : 0 ≤ (2*a^2+2*b^2)*((x-a*z)^2+(y-b*z)^2) := by positivity
  have h2 : 0 ≤ z^2 := sq_nonneg z
  nlinarith

theorem graph_metric_form (a b x y z : ℝ) :
    x^2+y^2+(1+a^2+b^2)*z^2-2*a*x*z-2*b*y*z =
      (x-a*z)^2+(y-b*z)^2+z^2 := by ring

end OQ14.Packet05GraphMetric
#print axioms OQ14.Packet05GraphMetric.graph_metric_coercive
#print axioms OQ14.Packet05GraphMetric.graph_metric_form

import Packet05GraphMetric

/-! Complex Hermitian coercivity for the graph-flattened metric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetricComplex
open OQ14.Packet05GraphMetric

theorem complex_graph_metric_coercive (a b : ℝ) (x y z : ℂ) :
    Complex.normSq x + Complex.normSq y + Complex.normSq z ≤
      (2+2*a^2+2*b^2) *
        (Complex.normSq (x-(a : ℂ)*z) + Complex.normSq (y-(b : ℂ)*z) + Complex.normSq z) := by
  have hr := graph_metric_coercive a b x.re y.re z.re
  have hi := graph_metric_coercive a b x.im y.im z.im
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at ⊢
  nlinarith

end OQ14.Packet05GraphMetricComplex
#print axioms OQ14.Packet05GraphMetricComplex.complex_graph_metric_coercive

import Packet05UniformGraphMetric

/-! The matching upper bound for the graph metric, with the same explicit
uniform constant as the lower bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetricUpper

theorem real_graph_metric_upper (a b M x y z : ℝ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    (x-a*z)^2+(y-b*z)^2+z^2 ≤ (2+4*M^2)*(x^2+y^2+z^2) := by
  have ha2 : a^2 ≤ M^2 := by nlinarith [sq_abs a, abs_nonneg a]
  have hb2 : b^2 ≤ M^2 := by nlinarith [sq_abs b, abs_nonneg b]
  have hx : (x-a*z)^2 ≤ 2*x^2 + 2*a^2*z^2 := by
    nlinarith [sq_nonneg (x+a*z)]
  have hy : (y-b*z)^2 ≤ 2*y^2 + 2*b^2*z^2 := by
    nlinarith [sq_nonneg (y+b*z)]
  have hz : 0 ≤ (4*M^2-2*a^2-2*b^2)*z^2 :=
    mul_nonneg (by nlinarith) (sq_nonneg z)
  have hxy : 0 ≤ 4*M^2*(x^2+y^2) := by positivity
  nlinarith

theorem complex_graph_metric_upper (a b M : ℝ) (x y z : ℂ)
    (ha : |a| ≤ M) (hb : |b| ≤ M) :
    Complex.normSq (x-(a : ℂ)*z) + Complex.normSq (y-(b : ℂ)*z) + Complex.normSq z ≤
      (2+4*M^2)*(Complex.normSq x+Complex.normSq y+Complex.normSq z) := by
  have hr := real_graph_metric_upper a b M x.re y.re z.re ha hb
  have hi := real_graph_metric_upper a b M x.im y.im z.im ha hb
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at ⊢
  nlinarith

end OQ14.Packet05GraphMetricUpper
#print axioms OQ14.Packet05GraphMetricUpper.real_graph_metric_upper
#print axioms OQ14.Packet05GraphMetricUpper.complex_graph_metric_upper

import Packet05GraphChartMatrix

/-! Exact Hermitian quadratic form of the actual graph metric. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.unnecessarySeqFocus false
namespace OQ14.Packet05GraphHermitianForm
open OQ14.Packet05GraphChartMatrix
open scoped ComplexConjugate

theorem graph_metric_hermitian_form (a b : ℝ) (z : Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, conj (z i) * (metric a b i j : ℂ) * z j).re =
      Complex.normSq (z 0-(a : ℂ)*z 2) + Complex.normSq (z 1-(b : ℂ)*z 2) + Complex.normSq (z 2) := by
  simp [Fin.sum_univ_three, metric, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, pow_two]
  <;> ring

end OQ14.Packet05GraphHermitianForm
#print axioms OQ14.Packet05GraphHermitianForm.graph_metric_hermitian_form

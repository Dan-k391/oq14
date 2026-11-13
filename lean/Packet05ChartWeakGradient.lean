import Packet05ChartTestTransport

/-! Signed Cartesian chart transport of actual global L² scalar weak partials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ChartWeakGradient
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05ChartOrientationMeasure OQ14.Packet05ChartBasis
  OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartTestTransport

def chartPull (up : Bool) (i : Fin 3) (u : L2Scalar) : L2Scalar :=
  Lp.compMeasurePreserving (inverseOriented up i) (oriented_inverse_measure_preserving up i) u

theorem chartPull_ae (up : Bool) (i : Fin 3) (u : L2Scalar) :
    (fun x => chartPull up i u x) =ᵐ[volume] fun x => u (inverseOriented up i x) :=
  Lp.coeFn_compMeasurePreserving u (oriented_inverse_measure_preserving up i)

theorem chart_change_variables (up : Bool) (i : Fin 3) (f : Space → ℂ) :
    (∫ y, f (orientedLinear up i y)) = ∫ x, f x := by
  have hm : MeasurePreserving (orientedLinear up i) (volume : Measure Space) volume :=
    oriented_coordinates_measure_preserving up i
  apply hm.integral_comp _ f
  exact (orientedHomeomorph up i).measurableEmbedding

theorem forward_value_pair (up : Bool) (i : Fin 3) (φ : Test) (u : L2Scalar) :
    valuePair (forwardTest up i φ) u = valuePair φ (chartPull up i u) := by
  simp only [valuePair,testPair_integral]
  rw [← chart_change_variables up i (fun x => chartPull up i u x * φ.function x)]
  apply integral_congr_ae
  have hm : MeasurePreserving (orientedLinear up i) (volume : Measure Space) volume :=
    oriented_coordinates_measure_preserving up i
  filter_upwards [hm.quasiMeasurePreserving.ae (chartPull_ae up i u)] with y hy
  rw [hy]
  have hinv : inverseOriented up i (orientedLinear up i y) = y := inverse_oriented_left up i y
  rw [hinv]
  rfl

theorem forward_derivative_pair (up : Bool) (i j : Fin 3) (φ : Test) (u : L2Scalar) :
    derivativePair (forwardTest up i φ) (Equiv.swap i 2 j) u =
      (chartSign up j : ℂ) * derivativePair φ j (chartPull up i u) := by
  simp only [derivativePair,testPair_integral]
  rw [← integral_const_mul, ← chart_change_variables up i
    (fun x => (chartSign up j : ℂ) * (chartPull up i u x * dcoord φ.function x j))]
  apply integral_congr_ae
  have hm : MeasurePreserving (orientedLinear up i) (volume : Measure Space) volume :=
    oriented_coordinates_measure_preserving up i
  filter_upwards [hm.quasiMeasurePreserving.ae (chartPull_ae up i u)] with y hy
  rw [hy,forward_test_partial]
  have hinv : inverseOriented up i (orientedLinear up i y) = y := inverse_oriented_left up i y
  rw [hinv]
  ring

theorem chart_weak_partial (up : Bool) (i j : Fin 3) (u D : L2Scalar)
    (hD : HasWeakPartial u D (Equiv.swap i 2 j)) :
    HasWeakPartial (chartPull up i u) ((chartSign up j : ℂ) • chartPull up i D) j := by
  intro φ
  have h := hD (forwardTest up i φ)
  rw [forward_value_pair,forward_derivative_pair] at h
  simp only [map_smul,smul_eq_mul]
  cases up <;> fin_cases j <;> simp [chartSign] at h ⊢ <;> first | exact h | linear_combination -h

end OQ14.Packet05ChartWeakGradient
#print axioms OQ14.Packet05ChartWeakGradient.chartPull_ae
#print axioms OQ14.Packet05ChartWeakGradient.chart_change_variables
#print axioms OQ14.Packet05ChartWeakGradient.forward_value_pair
#print axioms OQ14.Packet05ChartWeakGradient.forward_derivative_pair
#print axioms OQ14.Packet05ChartWeakGradient.chart_weak_partial

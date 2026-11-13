import Packet05ChartWeakGradient

/-! Regional scalar Gauss equations transform covariantly under either
signed Cartesian orientation, with the vector components transformed too. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ChartWeakDivergence
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05ChartOrientation
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartTestTransport
  OQ14.Packet05ChartWeakGradient

def chartVector (up : Bool) (i : Fin 3) (P : L2Vector) : L2Vector := fun j =>
  (chartSign up j : ℂ) • chartPull up i (P (Equiv.swap i 2 j))

theorem forward_test_support (up : Bool) (i : Fin 3) (φ : Test)
    (V W : Set Space) (hφ : tsupport φ.function ⊆ W)
    (hmap : ∀ x ∈ W, inverseOriented up i x ∈ V) :
    tsupport (forwardTest up i φ).function ⊆ V := by
  have hs : tsupport (forwardTest up i φ).function ⊆ (orientedLinear up i) ⁻¹' tsupport φ.function := by
    apply closure_minimal
    · intro y hy
      exact subset_tsupport _ hy
    · exact (isClosed_tsupport φ.function).preimage (orientedLinear up i).toContinuousLinearMap.continuous
  intro y hy
  have hx : orientedLinear up i y ∈ W := hφ (hs hy)
  have hm := hmap _ hx
  have hinv : inverseOriented up i (orientedLinear up i y) = y := inverse_oriented_left up i y
  simpa only [hinv] using hm

theorem chart_regional_divergence (up : Bool) (i : Fin 3) (V W : Set Space)
    (P : L2Vector) (D : L2Scalar) (hdiv : HasDivergenceOn V P D)
    (hmap : ∀ x ∈ W, inverseOriented up i x ∈ V) :
    HasDivergenceOn W (chartVector up i P) (chartPull up i D) := by
  intro φ hφ
  have h := hdiv (forwardTest up i φ) (forward_test_support up i φ V W hφ hmap)
  rw [forward_value_pair] at h
  have h0 := forward_derivative_pair up i 0 φ (P (Equiv.swap i 2 0))
  have h1 := forward_derivative_pair up i 1 φ (P (Equiv.swap i 2 1))
  have h2 := forward_derivative_pair up i 2 φ (P (Equiv.swap i 2 2))
  simp only [chartVector,map_smul,smul_eq_mul]
  fin_cases i <;> cases up <;>
    simp [chartSign,Equiv.swap_apply_def] at h0 h1 h2 h ⊢ <;>
    linear_combination h-h0-h1-h2

end OQ14.Packet05ChartWeakDivergence
#print axioms OQ14.Packet05ChartWeakDivergence.forward_test_support
#print axioms OQ14.Packet05ChartWeakDivergence.chart_regional_divergence

import ComplexInterfaceWeak

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexWeakFirstOrder
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexInterfaceWeak OQ14.ComplexResponseRealWeak
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def magneticPair (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  (I*z)⁻¹ * MagneticResponse.curlPair (pair c z S T u) i f

theorem electric_curl (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (u : VectorL2) (i : Fin 3) (f : Test) :
    MagneticResponse.curlPair (pair c z S T u) i f = I*z*magneticPair c z S T u i f := by
  have h : I*z ≠ 0 := mul_ne_zero I_ne_zero hz
  change _ = (I*z)*((I*z)⁻¹ * _)
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem magnetic_curl (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    MagneticResponse.curlPair (magneticPair c z S T u) i f =
      -I*z*displacementPair c z S T u i f := by
  calc
    _ = (I*z)⁻¹ * MagneticResponse.curlPair (MagneticResponse.curlPair (pair c z S T u)) i f := by
      unfold magneticPair MagneticResponse.curlPair
      ring
    _ = (I*z)⁻¹ * (z^2 * displacementPair c z S T u i f) := by
      rw [ComplexInterfaceWeak.curlcurl c z S T hST u hc i f hf]
    _ = _ := by
      field_simp [I_ne_zero, hz]
      ring_nf
      simp [Complex.I_sq]
#print axioms OQ14.ComplexWeakFirstOrder.electric_curl
#print axioms OQ14.ComplexWeakFirstOrder.magnetic_curl
end OQ14.ComplexWeakFirstOrder


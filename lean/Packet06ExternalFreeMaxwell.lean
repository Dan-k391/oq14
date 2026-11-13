import Packet06GreenSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ExternalFreeMaxwell
open MeasureTheory Metric Set Maxwell Packet06LocalPencil Packet06GreenSource DynamicSource ComplexResponseTests
abbrev VectorL2 := VectorFourier.VectorL2

def supportCoefficient (J : ℝ) : StaticCoefficient.Coefficient where
  value ξ := (closedBall (0 : Space) J).indicator (fun _ => (1 : ℝ)) (VectorFourier.coordinateMap.symm ξ)
  bound := 1
  measurable := (measurable_const.indicator measurableSet_closedBall).comp VectorFourier.coordinateMap.symm.measurable
  nonnegative ξ := by
    classical
    by_cases h : VectorFourier.coordinateMap.symm ξ ∈ closedBall (0 : Space) J <;> simp [h]
  bounded ξ := by
    classical
    by_cases h : VectorFourier.coordinateMap.symm ξ ∈ closedBall (0 : Space) J <;> simp [h]

theorem supportCoefficient_spatial (J : ℝ) (x : Space) :
    (supportCoefficient J).value (VectorFourier.coordinateMap x) =
      (closedBall (0 : Space) J).indicator (fun _ => (1 : ℝ)) x := by
  simp [supportCoefficient]

theorem supportCoefficient_support (J : ℝ) :
    ∀ x : Space, x ∉ closedBall 0 J → (supportCoefficient J).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  simp [supportCoefficient_spatial,hx]

theorem supported_multiplier_identity (J : ℝ) (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    StaticCoefficient.sqrtMultiplier (supportCoefficient J) f = f := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hmul := StaticNewton.material_source_ae (supportCoefficient J) f i
  have hcoord := NewtonL2.physicalCoordinate_ae f i
  have hout := NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier (supportCoefficient J) f) i
  filter_upwards [hmul,hcoord,hf,hout] with x hm hco hx ho
  rw [← ho,hm,← hco,supportCoefficient_spatial]
  by_cases h : x ∈ closedBall (0 : Space) J
  · simp [h]
  · have hz := hx h
    simp [h,hco,hz]

/-- The truncated dyadic kernel is the actual direct Maxwell source solution
on any observation ball for any L² current supported in the source ball. -/
theorem free_maxwell_test (z : ℂ) (hz : z ≠ 0) (J T : ℝ) (hJT : 0 ≤ T+J)
    (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (φ : Test) (hφ : tsupport (φ.val : Space → ℂ) ⊆ closedBall 0 T) :
    curlCurlTest i φ ((z^2)⁻¹ • kernel z J T f) -
      z^2 * testPair i φ.val ((z^2)⁻¹ • kernel z J T f) = testPair i φ.val f := by
  have h := response_source_test (supportCoefficient J) z J T hJT f (supportCoefficient_support J) i φ hφ
  rw [show response (supportCoefficient J) z J T f = kernel z J T f by
    change kernel z J T (StaticCoefficient.sqrtMultiplier (supportCoefficient J) f) = _
    rw [supported_multiplier_identity J f hf], supported_multiplier_identity J f hf] at h
  simp only [map_smul,smul_eq_mul]
  have hz2 : z^2 ≠ 0 := pow_ne_zero 2 hz
  field_simp
  linear_combination h

#print axioms OQ14.Packet06ExternalFreeMaxwell.supportCoefficient_spatial
#print axioms OQ14.Packet06ExternalFreeMaxwell.supportCoefficient_support
#print axioms OQ14.Packet06ExternalFreeMaxwell.supported_multiplier_identity
#print axioms OQ14.Packet06ExternalFreeMaxwell.free_maxwell_test
end OQ14.Packet06ExternalFreeMaxwell

import Packet06BallObservation
import ComplexExteriorResponse

/-! Direct electric source convention for the actual local volume inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06GreenSource
open MeasureTheory Metric Packet06LocalPencil Packet06Observation ComplexResponseTests
open DynamicSource
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def curlCurlTest (i : Fin 3) (f : Test) : VectorL2 →L[ℂ] ℂ :=
  (∑ l : Fin 3, testPair l (testPartial l (testPartial i f)).val) -
    (∑ l : Fin 3, testPair i (testPartial l (testPartial l f)).val)

def maxwellTest (c : Coefficient) (z : ℂ) (i : Fin 3) (f : Test) : VectorL2 →L[ℂ] ℂ :=
  curlCurlTest i f - z^2 • (testPair i f.val).comp
    (1+StaticCoefficient.sqrtMultiplier c*StaticCoefficient.sqrtMultiplier c)

theorem response_source_test (c : Coefficient) (z : ℂ) (S T : ℝ) (hST : 0 ≤ T+S)
    (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    curlCurlTest i f (response c z S T u) = z^2 *
      (testPair i f.val (response c z S T u) + testPair i f.val (StaticCoefficient.sqrtMultiplier c u)) := by
  have h := ComplexExteriorResponse.residual_zero c S T hST u hc i f hf z
  unfold ComplexExteriorResponse.residual at h
  simp only [←response_actual] at h
  have hs : testPair i f.val (StaticCoefficient.sqrtMultiplier c u) =
      ∫ x, DynamicVolume.source c u i x * f.val x := by
    rw [testPair_integral]
    apply integral_congr_ae
    filter_upwards [NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c u) i,
      StaticNewton.material_source_ae c u i] with x hp hs
    rw [←hp,hs]
    rfl
  rw [hs]
  change (∑ l : Fin 3, testPair l (testPartial l (testPartial i f)).val (response c z S T u))-
    (∑ l : Fin 3, testPair i (testPartial l (testPartial l f)).val (response c z S T u)) = _
  change _-_-z^2*testPair i f.val (response c z S T u)-
    z^2*(∫ x, DynamicVolume.source c u i x*f.val x) = 0 at h
  linear_combination h

theorem solved_weighted_response (c : Coefficient) (z : ℂ) (S T : ℝ) (hST : S ≤ T)
    (u f : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = f) :
    StaticCoefficient.sqrtMultiplier c (response c z S T u) = u-f := by
  rw [weighted_observation_independent c z S T hST u hc]
  rw [weighted_block_eq] at hu
  change u-StaticCoefficient.sqrtMultiplier c (response c z S S u) = f at hu
  apply eq_sub_iff_add_eq.mpr
  rw [←hu]
  abel

theorem solved_maxwell_test (c : Coefficient) (z : ℂ) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u g : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = g)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    maxwellTest c z i f (response c z S T u) = z^2 * testPair i f.val (StaticCoefficient.sqrtMultiplier c g) := by
  have hsource := response_source_test c z S T hplus u hc i f hf
  have hweighted := solved_weighted_response c z S T hST u g hc hu
  change curlCurlTest i f (response c z S T u) -
    z^2*(testPair i f.val (response c z S T u+
      StaticCoefficient.sqrtMultiplier c (StaticCoefficient.sqrtMultiplier c (response c z S T u)))) = _
  rw [hweighted,map_sub,map_add,map_sub,hsource]
  ring

theorem direct_source_green (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : IsUnit (ComplexConvolutionAnalytic.volumeBlock c z S)) (g : VectorL2)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    maxwellTest c z i f ((z^2)⁻¹ • response c z S T
      (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z S) g)) =
        testPair i f.val (StaticCoefficient.sqrtMultiplier c g) := by
  have he : ComplexConvolutionAnalytic.volumeBlock c z S
      (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z S) g) = g :=
    congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L g) (Ring.mul_inverse_cancel _ hu)
  rw [map_smul,solved_maxwell_test c z S T hST hplus _ g hc he i f hf,smul_eq_mul,
    ←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hz),one_mul]

end OQ14.Packet06GreenSource
#print axioms OQ14.Packet06GreenSource.response_source_test
#print axioms OQ14.Packet06GreenSource.solved_weighted_response
#print axioms OQ14.Packet06GreenSource.solved_maxwell_test
#print axioms OQ14.Packet06GreenSource.direct_source_green

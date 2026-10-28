import ComplexResponseOverlap
import ComplexSphereWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexInterfaceWeak
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexResponseTests OQ14.ComplexResponseRealWeak OQ14.ComplexSphereWeak
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def pair (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  testPair i f.val (ComplexExteriorResponse.response c z S T u)

def displacementPair (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  pair c z S T u i f + ∫ x, DynamicVolume.source c u i x * f.val x

theorem curlcurl (c : Coefficient) (z : ℂ) (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    MagneticResponse.curlPair (MagneticResponse.curlPair (pair c z S T u)) i f =
      z^2 * displacementPair c z S T u i f := by
  have h := ComplexExteriorResponse.residual_zero c S T hST u hc i f hf z
  rw [MagneticResponse.curlPair_curlPair]
  dsimp only [ComplexExteriorResponse.residual, displacementPair, pair] at *
  linear_combination h

theorem displacement_divergence_zero (c : Coefficient) (z : ℂ) (hz : z ≠ 0)
    (S T : ℝ) (hST : 0 ≤ T+S) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    (∑ j : Fin 3, displacementPair c z S T u j (testPartial j f)) = 0 := by
  have h := div_curl (MagneticResponse.curlPair (pair c z S T u)) f
  have he (j : Fin 3) := curlcurl c z S T hST u hc j (testPartial j f) ((partial_support j f).trans hf)
  simp_rw [he] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hz)

#print axioms OQ14.ComplexInterfaceWeak.curlcurl
#print axioms OQ14.ComplexInterfaceWeak.displacement_divergence_zero
end OQ14.ComplexInterfaceWeak

import ComplexExteriorResponse
import ComplexSphereWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexExteriorWeak
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexResponseTests OQ14.ComplexExteriorResponse OQ14.ComplexSphereWeak
  OQ14.ComplexResponseRealWeak
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

def pair (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  testPair i f.val (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u)

theorem source_pair_zero (n : ℝ) (hn : 1 < n) (u : VectorL2) (i : Fin 3) (f : Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ) :
    (∫ x, DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i x * f.val x) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) 1
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hf h hx)
    simp [hz]
  · rw [DynamicVolume.source_zero _ _ 1 (ModalWeightedMode.coefficient_support n hn) i x hx]
    simp

theorem curlcurl (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 0 ≤ T+1)
    (u : VectorL2) (i : Fin 3) (f : Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T)
    (ho : tsupport (f.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ) :
    MagneticResponse.curlPair (MagneticResponse.curlPair (pair n hn z T u)) i f =
      z^2 * pair n hn z T u i f := by
  have h := ComplexExteriorResponse.residual_zero (ModalWeightedMode.coefficient n hn) 1 T hT u
    (ModalWeightedMode.coefficient_support n hn) i f hf z
  rw [MagneticResponse.curlPair_curlPair]
  unfold ComplexExteriorResponse.residual at h
  rw [source_pair_zero n hn u i f ho] at h
  dsimp only [pair] at *
  linear_combination h

theorem divergence_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2) (f : Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T)
    (ho : tsupport (f.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ) :
    (∑ j : Fin 3, pair n hn z T u j (testPartial j f)) = 0 := by
  have h := div_curl (MagneticResponse.curlPair (pair n hn z T u)) f
  have he (j : Fin 3) := curlcurl n hn z T hT u j (testPartial j f)
    ((partial_support j f).trans hf) ((partial_support j f).trans ho)
  simp_rw [he] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hz)

theorem component_helmholtz_test (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2) (i : Fin 3) (f : Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T)
    (ho : tsupport (f.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ) :
    (∑ j : Fin 3, pair n hn z T u i (testPartial j (testPartial j f))) +
      z^2 * pair n hn z T u i f = 0 := by
  have hc := curlcurl n hn z T hT u i f hf ho
  rw [MagneticResponse.curlPair_curlPair] at hc
  have hd := divergence_zero n hn z hz T hT u (testPartial i f)
    ((partial_support i f).trans hf) ((partial_support i f).trans ho)
  linear_combination hd - hc

#print axioms OQ14.ComplexExteriorWeak.source_pair_zero
#print axioms OQ14.ComplexExteriorWeak.curlcurl
#print axioms OQ14.ComplexExteriorWeak.divergence_zero
#print axioms OQ14.ComplexExteriorWeak.component_helmholtz_test
end OQ14.ComplexExteriorWeak


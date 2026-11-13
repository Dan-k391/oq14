import Packet05DivergenceUpgrade
import KernelSource

/-! Distributional partial derivatives commute with weak curl. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05CurlCommutation
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.PartialSmoothing OQ14.DivCurlCompact
open scoped Topology SchwartzMap

def partialTest (φ : Test) (hφ : ContDiff ℝ 2 φ.function) (i : Fin 3) : Test :=
  ⟨fun x => dcoord φ.function x i, KernelSource.partial_contDiff hφ i,
    φ.compact.fderiv_apply ℝ (basis i)⟩

theorem derivativePair_partial_comm (φ : Test) (hφ : ContDiff ℝ 2 φ.function)
    (i j : Fin 3) (u : L2Scalar) :
    derivativePair (partialTest φ hφ i) j u = derivativePair (partialTest φ hφ j) i u := by
  simp only [derivativePair, testPair_integral, partialTest]
  apply integral_congr_ae
  filter_upwards with x
  rw [partial_comm hφ x j i]

theorem smooth_curl_to_weak (E C : L2Vector)
    (h : ∀ φ : Test, ContDiff ℝ 2 φ.function → ∀ j : Fin 3,
      weakCurl φ j E - valuePair φ (C j) = 0) : HasWeakCurl E C := by
  intro φ j
  let ψ : DomainCurl.Test Set.univ := ⟨φ, Set.subset_univ _⟩
  obtain ⟨K, f, hK, _, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation isOpen_univ ψ
  let t : ℕ → Test := fun n => ⟨f n, (f n).smooth 1,
    hK.of_isClosed_subset isClosed_closure (hfK n)⟩
  have ht (n : ℕ) : ContDiff ℝ 2 (t n).function := (f n).smooth 2
  have hv (n : ℕ) :
      scalarProduct (E (next j)) (FourierL2.embed (GradientProjection.pderivative (previous j) (f n))) -
      scalarProduct (E (previous j)) (FourierL2.embed (GradientProjection.pderivative (next j) (f n))) -
      scalarProduct (C j) (FourierL2.embed (f n)) = 0 := by
    have hh := h (t n) (ht n) j
    simp only [weakCurl, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, valuePair, derivativePair, testPair_integral] at hh
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, t] using hh
  have hlim := (((scalarProduct (E (next j))).continuous.tendsto _ |>.comp (hd (previous j))).sub
    ((scalarProduct (E (previous j))).continuous.tendsto _ |>.comp (hd (next j)))).sub
    ((scalarProduct (C j)).continuous.tendsto _ |>.comp hf)
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hv n).symm)))
  change weakCurl φ j E - valuePair φ (C j) = 0
  simpa only [ψ, testL2, testDerivativeL2, scalarProduct_continuousL2, weakCurl,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, valuePair, derivativePair] using hz

theorem partial_commutes_weakCurl (E C G J : L2Vector) (i : Fin 3)
    (hcurl : HasWeakCurl E C) (hE : ∀ j, HasWeakPartial (E j) (G j) i)
    (hC : ∀ j, HasWeakPartial (C j) (J j) i) : HasWeakCurl G J := by
  apply smooth_curl_to_weak
  intro φ hφ j
  let ψ := partialTest φ hφ i
  let α := partialTest φ hφ (previous j)
  let β := partialTest φ hφ (next j)
  have hcurlψ := hcurl ψ j
  have h1 := hE (next j) α
  have h2 := hE (previous j) β
  have h3 := hC j φ
  have ha : derivativePair ψ (previous j) (E (next j)) =
      derivativePair α i (E (next j)) := derivativePair_partial_comm φ hφ i (previous j) _
  have hb : derivativePair ψ (next j) (E (previous j)) =
      derivativePair β i (E (previous j)) := derivativePair_partial_comm φ hφ i (next j) _
  change derivativePair ψ (previous j) (E (next j)) -
    derivativePair ψ (next j) (E (previous j)) - valuePair ψ (C j) = 0 at hcurlψ
  change valuePair α (G (next j)) + derivativePair α i (E (next j)) = 0 at h1
  change valuePair β (G (previous j)) + derivativePair β i (E (previous j)) = 0 at h2
  change valuePair φ (J j) + valuePair ψ (C j) = 0 at h3
  change derivativePair φ (previous j) (G (next j)) -
    derivativePair φ (next j) (G (previous j)) - valuePair φ (J j) = 0
  have hα : valuePair α (G (next j)) = derivativePair φ (previous j) (G (next j)) := rfl
  have hβ : valuePair β (G (previous j)) = derivativePair φ (next j) (G (previous j)) := rfl
  rw [ha, hb] at hcurlψ
  rw [hα] at h1
  rw [hβ] at h2
  linear_combination -hcurlψ + h1 - h2 - h3

end OQ14.Packet05CurlCommutation
#print axioms OQ14.Packet05CurlCommutation.derivativePair_partial_comm
#print axioms OQ14.Packet05CurlCommutation.smooth_curl_to_weak
#print axioms OQ14.Packet05CurlCommutation.partial_commutes_weakCurl

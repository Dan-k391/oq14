import Packet05CurlCommutation

/-! Recovery of a second normal derivative from a genuine weak Laplacian and
two already obtained tangential second derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05NormalSecond
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.PartialSmoothing OQ14.DivCurlCompact OQ14.Packet05CurlCommutation
open scoped Topology SchwartzMap

def HasSmoothWeakLaplacian (u f : L2Scalar) : Prop :=
  ∀ (φ : Test) (hφ : ContDiff ℝ 2 φ.function),
    valuePair φ f = derivativePair (partialTest φ hφ 0) 0 u +
      derivativePair (partialTest φ hφ 1) 1 u +
      derivativePair (partialTest φ hφ 2) 2 u

theorem smooth_partial_to_weak (u v : L2Scalar) (i : Fin 3)
    (h : ∀ φ : Test, ContDiff ℝ 2 φ.function →
      valuePair φ v + derivativePair φ i u = 0) : HasWeakPartial u v i := by
  intro φ
  let ψ : DomainCurl.Test Set.univ := ⟨φ, Set.subset_univ _⟩
  obtain ⟨K, f, hK, _, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation isOpen_univ ψ
  let t : ℕ → Test := fun n => ⟨f n, (f n).smooth 1,
    hK.of_isClosed_subset isClosed_closure (hfK n)⟩
  have ht (n : ℕ) : ContDiff ℝ 2 (t n).function := (f n).smooth 2
  have hv (n : ℕ) : scalarProduct v (FourierL2.embed (f n)) +
      scalarProduct u (FourierL2.embed (GradientProjection.pderivative i (f n))) = 0 := by
    have hh := h (t n) (ht n)
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, valuePair,
      derivativePair, testPair_integral, t] using hh
  have hlim := ((scalarProduct v).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct u).continuous.tendsto _ |>.comp (hd i))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hv n).symm)))
  simpa only [ψ, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

theorem normal_second_from_laplacian (u f D0 D1 D2 G00 G11 : L2Scalar)
    (hlap : HasSmoothWeakLaplacian u f)
    (h0 : HasWeakPartial u D0 0) (h1 : HasWeakPartial u D1 1)
    (h2 : HasWeakPartial u D2 2)
    (h00 : HasWeakPartial D0 G00 0) (h11 : HasWeakPartial D1 G11 1) :
    HasWeakPartial D2 (f - G00 - G11) 2 := by
  apply smooth_partial_to_weak
  intro φ hφ
  have hL := hlap φ hφ
  have ha := h0 (partialTest φ hφ 0)
  have hb := h1 (partialTest φ hφ 1)
  have hc := h2 (partialTest φ hφ 2)
  have hd := h00 φ
  have he := h11 φ
  change derivativePair φ 0 D0 + derivativePair (partialTest φ hφ 0) 0 u = 0 at ha
  change derivativePair φ 1 D1 + derivativePair (partialTest φ hφ 1) 1 u = 0 at hb
  change derivativePair φ 2 D2 + derivativePair (partialTest φ hφ 2) 2 u = 0 at hc
  simp only [map_sub]
  linear_combination hL + ha + hb + hc - hd - he

/-- Mixed weak partials commute whenever the indicated L² representatives
exist; the reverse mixed derivative is obtained, not assumed. -/
theorem weak_mixed_partial_commute (u Di Dj Vij : L2Scalar) (i j : Fin 3)
    (hi : HasWeakPartial u Di i) (hj : HasWeakPartial u Dj j)
    (hij : HasWeakPartial Di Vij j) : HasWeakPartial Dj Vij i := by
  apply smooth_partial_to_weak
  intro φ hφ
  have ha := hi (partialTest φ hφ j)
  have hb := hj (partialTest φ hφ i)
  have hc := hij φ
  have hd := derivativePair_partial_comm φ hφ j i u
  change derivativePair φ j Di + derivativePair (partialTest φ hφ j) i u = 0 at ha
  change derivativePair φ i Dj + derivativePair (partialTest φ hφ i) j u = 0 at hb
  linear_combination hc - ha + hb + hd

/-- A weak Laplacian and tangential derivatives of all first partials yield
the full Hessian, including the missing normal-normal derivative. -/
theorem hessian_from_tangential_and_laplacian (u f : L2Scalar) (D : Fin 3 → L2Scalar)
    (hfirst : ∀ i, HasWeakPartial u (D i) i)
    (htan : ∀ i, i ≠ 2 → ∀ j, ∃ v, HasWeakPartial (D j) v i)
    (hlap : HasSmoothWeakLaplacian u f) :
    ∃ H : Fin 3 → Fin 3 → L2Scalar, ∀ i j, HasWeakPartial (D j) (H i j) i := by
  have hall : ∀ i j, ∃ v, HasWeakPartial (D j) v i := by
    intro i j
    by_cases hi : i = 2
    · subst i
      fin_cases j
      · obtain ⟨v, hv⟩ := htan 0 (by decide) 2
        exact ⟨v, weak_mixed_partial_commute u (D 2) (D 0) v 2 0 (hfirst 2) (hfirst 0) hv⟩
      · obtain ⟨v, hv⟩ := htan 1 (by decide) 2
        exact ⟨v, weak_mixed_partial_commute u (D 2) (D 1) v 2 1 (hfirst 2) (hfirst 1) hv⟩
      · obtain ⟨v0, hv0⟩ := htan 0 (by decide) 0
        obtain ⟨v1, hv1⟩ := htan 1 (by decide) 1
        exact ⟨f-v0-v1, normal_second_from_laplacian u f (D 0) (D 1) (D 2) v0 v1
          hlap (hfirst 0) (hfirst 1) (hfirst 2) hv0 hv1⟩
    · exact htan i hi j
  classical
  choose H hH using hall
  exact ⟨H, hH⟩

end OQ14.Packet05NormalSecond
#print axioms OQ14.Packet05NormalSecond.smooth_partial_to_weak
#print axioms OQ14.Packet05NormalSecond.normal_second_from_laplacian
#print axioms OQ14.Packet05NormalSecond.weak_mixed_partial_commute
#print axioms OQ14.Packet05NormalSecond.hessian_from_tangential_and_laplacian

import WeakPoynting.PartialSmoothing

/-! Actual compact divergence-graph smoothing and weak gradient/divergence duality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.WeakDivergenceGraph
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.PartialSmoothing Filter
open scoped Topology SchwartzMap

theorem compact_divergence_graph_approximation {E : L2Vector} {D : L2Scalar}
    (hE : ∀ i, CompactRepresentative (E i)) (hD : HasWeakDivergence E D) :
    ∃ f : ℕ → Fin 3 → 𝓢(Space, ℂ),
      (∀ n i, HasCompactSupport (f n i : Space → ℂ)) ∧
      (∀ i, Tendsto (fun n => FourierL2.embed (f n i)) atTop (𝓝 (E i))) ∧
      Tendsto (fun n => FourierL2.embed (GradientProjection.divergence (f n))) atTop (𝓝 D) := by
  refine ⟨fun n => smoothSchwartzField (shrinkingBump n) E hE,?_,?_,?_⟩
  · intro n i
    exact smoothScalar_compact _ (complexKernel_compact _) (E i) (hE i)
  · intro i
    simp only [smoothSchwartzField,embed_smoothSchwartz]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (E i)
  · simp only [embed_divergence_smoothSchwartz _ hE hD]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto D

theorem weak_gradient_divergence_pairing (u : L2Scalar) (G E : L2Vector) (D : L2Scalar)
    (hG : ∀ i, HasWeakPartial u (G i) i) (hE : ∀ i, CompactRepresentative (E i))
    (hD : HasWeakDivergence E D) :
    (∑ i : Fin 3, scalarProduct (G i) (E i))+scalarProduct u D=0 := by
  obtain ⟨f,hc,hf,hd⟩ := compact_divergence_graph_approximation hE hD
  have hl := ((((scalarProduct (G 0)).continuous.tendsto _ |>.comp (hf 0)).add
    ((scalarProduct (G 1)).continuous.tendsto _ |>.comp (hf 1))).add
    ((scalarProduct (G 2)).continuous.tendsto _ |>.comp (hf 2))).add
    ((scalarProduct u).continuous.tendsto _ |>.comp hd)
  have hp (n : ℕ) (i : Fin 3) :
      scalarProduct (G i) (FourierL2.embed (f n i))+
        scalarProduct u (FourierL2.embed (GradientProjection.pderivative i (f n i)))=0 := by
    have h := hG i ⟨f n i,(f n i).smooth 1,hc n i⟩
    simpa only [HasWeakPartial,valuePair,derivativePair,testPair_integral,
      scalarProduct_embed,GradientProjection.pderivative_apply] using h
  have hz (n : ℕ) :
      scalarProduct (G 0) (FourierL2.embed (f n 0))+
      scalarProduct (G 1) (FourierL2.embed (f n 1))+
      scalarProduct (G 2) (FourierL2.embed (f n 2))+
      scalarProduct u (FourierL2.embed (GradientProjection.divergence (f n)))=0 := by
    simp only [GradientProjection.divergence,map_add]
    linear_combination hp n 0+hp n 1+hp n 2
  have he := tendsto_nhds_unique hl
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hz n).symm)))
  simpa only [Fin.sum_univ_three] using he

theorem weak_gradient_divergence_integral (u : L2Scalar) (G E : L2Vector) (D : L2Scalar)
    (hG : ∀ i, HasWeakPartial u (G i) i) (hE : ∀ i, CompactRepresentative (E i))
    (hD : HasWeakDivergence E D) :
    (∑ i : Fin 3, ∫ x : Space, G i x*E i x)+(∫ x : Space, u x*D x)=0 := by
  simpa only [scalarProduct_integral] using weak_gradient_divergence_pairing u G E D hG hE hD

end OQ14.WeakDivergenceGraph

#print axioms OQ14.WeakDivergenceGraph.compact_divergence_graph_approximation
#print axioms OQ14.WeakDivergenceGraph.weak_gradient_divergence_pairing
#print axioms OQ14.WeakDivergenceGraph.weak_gradient_divergence_integral

import Packet05ScalarDifferencePartial
import WeakPoynting.PartialSmoothing

/-! A whole-space weak divergence identity can be tested against any compactly
supported scalar H¹ function, by actual simultaneous mollifier convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarH1Testing
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.PartialSmoothing
open scoped Topology SchwartzMap

theorem weak_divergence_test_compact_h1 (E : L2Vector) (D u : L2Scalar)
    (G : Fin 3 → L2Scalar) (hdiv : HasWeakDivergence E D)
    (hu : CompactRepresentative u) (hG : ∀ i, HasWeakPartial u (G i) i) :
    scalarProduct D u + scalarProduct (E 0) (G 0) +
      scalarProduct (E 1) (G 1) + scalarProduct (E 2) (G 2) = 0 := by
  let f : ℕ → 𝓢(Space, ℂ) := fun n => smoothSchwartz (shrinkingBump n) u hu
  have hf : Tendsto (fun n => FourierL2.embed (f n)) atTop (𝓝 u) := by
    simp only [f, embed_smoothSchwartz]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto u
  have hg (i : Fin 3) : Tendsto (fun n =>
      FourierL2.embed (GradientProjection.pderivative i (f n))) atTop (𝓝 (G i)) := by
    simp only [f, embed_partial_smoothSchwartz _ hu (hG i)]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (G i)
  have hn (n : ℕ) : scalarProduct D (FourierL2.embed (f n)) +
      scalarProduct (E 0) (FourierL2.embed (GradientProjection.pderivative 0 (f n))) +
      scalarProduct (E 1) (FourierL2.embed (GradientProjection.pderivative 1 (f n))) +
      scalarProduct (E 2) (FourierL2.embed (GradientProjection.pderivative 2 (f n))) = 0 := by
    let φ : Test := ⟨f n, (f n).smooth 1,
      smoothScalar_compact _ (complexKernel_compact (shrinkingBump n)) u hu⟩
    have hh := hdiv φ
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, valuePair,
      derivativePair, testPair_integral, φ] using hh
  have hlim := (((scalarProduct D).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct (E 0)).continuous.tendsto _ |>.comp (hg 0))).add
    ((scalarProduct (E 1)).continuous.tendsto _ |>.comp (hg 1)) |>.add
    ((scalarProduct (E 2)).continuous.tendsto _ |>.comp (hg 2))
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hn n).symm)))

end OQ14.Packet05ScalarH1Testing
#print axioms OQ14.Packet05ScalarH1Testing.weak_divergence_test_compact_h1

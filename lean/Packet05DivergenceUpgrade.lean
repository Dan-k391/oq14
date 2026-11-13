import WeakPoynting.InteriorTestDensity
import WeakPoynting.LocalRegularity

/-! Upgrade a C2-test divergence identity to all compact C1 tests using
proved simultaneous value-and-gradient approximation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DivergenceUpgrade
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.PartialSmoothing OQ14.DivCurlCompact OQ14.LocalRegularity
open scoped Topology SchwartzMap

theorem smooth_divergence_to_weak (E : L2Vector) (D : L2Scalar)
    (h : HasSmoothWeakDivergence E D) : HasWeakDivergence E D := by
  intro φ
  let ψ : DomainCurl.Test Set.univ := ⟨φ, Set.subset_univ _⟩
  obtain ⟨K, f, hK, _, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation isOpen_univ ψ
  let t : ℕ → Test := fun n => ⟨f n, (f n).smooth 1,
    hK.of_isClosed_subset isClosed_closure (hfK n)⟩
  have ht (n : ℕ) : ContDiff ℝ 2 (t n).function := (f n).smooth 2
  have hv (n : ℕ) :
      scalarProduct D (FourierL2.embed (f n)) +
        scalarProduct (E 0) (FourierL2.embed (GradientProjection.pderivative 0 (f n))) +
        scalarProduct (E 1) (FourierL2.embed (GradientProjection.pderivative 1 (f n))) +
        scalarProduct (E 2) (FourierL2.embed (GradientProjection.pderivative 2 (f n))) = 0 := by
    have hh := h (t n) (ht n)
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, valuePair,
      derivativePair, testPair_integral, t] using hh
  have hlim := (((scalarProduct D).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct (E 0)).continuous.tendsto _ |>.comp (hd 0))).add
    ((scalarProduct (E 1)).continuous.tendsto _ |>.comp (hd 1)) |>.add
    ((scalarProduct (E 2)).continuous.tendsto _ |>.comp (hd 2))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hv n).symm)))
  simpa only [ψ, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

theorem normal_from_divergence (E : L2Vector) (D G0 G1 : L2Scalar)
    (hdiv : HasWeakDivergence E D)
    (h0 : HasWeakPartial (E 0) G0 0) (h1 : HasWeakPartial (E 1) G1 1) :
    HasWeakPartial (E 2) (D-G0-G1) 2 := by
  intro φ
  have hh := hdiv φ
  have h0 := h0 φ
  have h1 := h1 φ
  simp only [map_sub]
  linear_combination hh - h0 - h1

end OQ14.Packet05DivergenceUpgrade
#print axioms OQ14.Packet05DivergenceUpgrade.smooth_divergence_to_weak
#print axioms OQ14.Packet05DivergenceUpgrade.normal_from_divergence

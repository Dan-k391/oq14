import Packet05RegionalPartial
import Packet05DivergenceCommutation

/-! Regional weak divergence and commutation with a regional weak partial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalDivergence
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.Packet05CurlCommutation OQ14.Packet05RegionalPartial
open scoped Topology SchwartzMap

def HasDivergenceOn (V : Set Space) (E : L2Vector) (D : L2Scalar) : Prop :=
  ∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ D + derivativePair φ 0 (E 0) +
    derivativePair φ 1 (E 1) + derivativePair φ 2 (E 2) = 0

theorem global_divergence_on (V : Set Space) (E : L2Vector) (D : L2Scalar)
    (h : HasWeakDivergence E D) : HasDivergenceOn V E D := fun φ _ => h φ

theorem smooth_divergence_on_to_weak (V : Set Space) (hV : IsOpen V) (E : L2Vector) (D : L2Scalar)
    (h : ∀ φ : Test, ContDiff ℝ 2 φ.function → tsupport φ.function ⊆ V →
      valuePair φ D + derivativePair φ 0 (E 0) + derivativePair φ 1 (E 1) + derivativePair φ 2 (E 2) = 0) :
    HasDivergenceOn V E D := by
  intro φ hφV
  let ψ : DomainCurl.Test V := ⟨φ,hφV⟩
  obtain ⟨K,f,hK,hKV,hfK,hf,hd⟩ := InteriorTestDensity.interior_test_approximation hV ψ
  let t : ℕ → Test := fun n => ⟨f n,(f n).smooth 1,hK.of_isClosed_subset isClosed_closure (hfK n)⟩
  have hn (n : ℕ) : scalarProduct D (FourierL2.embed (f n)) +
      scalarProduct (E 0) (FourierL2.embed (GradientProjection.pderivative 0 (f n))) +
      scalarProduct (E 1) (FourierL2.embed (GradientProjection.pderivative 1 (f n))) +
      scalarProduct (E 2) (FourierL2.embed (GradientProjection.pderivative 2 (f n))) = 0 := by
    have ht := h (t n) ((f n).smooth 2) ((hfK n).trans hKV)
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, valuePair,
      derivativePair, testPair_integral, t] using ht
  have hl := (((scalarProduct D).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct (E 0)).continuous.tendsto _ |>.comp (hd 0))).add
    ((scalarProduct (E 1)).continuous.tendsto _ |>.comp (hd 1)) |>.add
    ((scalarProduct (E 2)).continuous.tendsto _ |>.comp (hd 2))
  have hz := tendsto_nhds_unique hl (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hn n).symm)))
  simpa only [ψ, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

theorem regional_partial_commutes_divergence (V : Set Space) (hV : IsOpen V)
    (E G : L2Vector) (D J : L2Scalar) (i : Fin 3)
    (hdiv : HasDivergenceOn V E D) (hE : ∀ j, HasPartialOn V (E j) (G j) i)
    (hD : HasPartialOn V D J i) : HasDivergenceOn V G J := by
  apply smooth_divergence_on_to_weak V hV
  intro φ hφ hφV
  have hs (l : Fin 3) : tsupport (partialTest φ hφ l).function ⊆ V :=
    (RegionalMaxwellHelmholtz.partial_tsupport φ.function l).trans hφV
  let ψ := partialTest φ hφ i
  have hdivψ := hdiv ψ (hs i)
  have hDφ := hD φ hφV
  have hE0 := hE 0 (partialTest φ hφ 0) (hs 0)
  have hE1 := hE 1 (partialTest φ hφ 1) (hs 1)
  have hE2 := hE 2 (partialTest φ hφ 2) (hs 2)
  have h0 := derivativePair_partial_comm φ hφ i 0 (E 0)
  have h1 := derivativePair_partial_comm φ hφ i 1 (E 1)
  have h2 := derivativePair_partial_comm φ hφ i 2 (E 2)
  change valuePair ψ D + derivativePair ψ 0 (E 0) + derivativePair ψ 1 (E 1) + derivativePair ψ 2 (E 2) = 0 at hdivψ
  rw [h0,h1,h2] at hdivψ
  change valuePair φ J + valuePair ψ D = 0 at hDφ
  change derivativePair φ 0 (G 0) + derivativePair (partialTest φ hφ 0) i (E 0) = 0 at hE0
  change derivativePair φ 1 (G 1) + derivativePair (partialTest φ hφ 1) i (E 1) = 0 at hE1
  change derivativePair φ 2 (G 2) + derivativePair (partialTest φ hφ 2) i (E 2) = 0 at hE2
  linear_combination -hdivψ + hDφ + hE0 + hE1 + hE2

end OQ14.Packet05RegionalDivergence
#print axioms OQ14.Packet05RegionalDivergence.global_divergence_on
#print axioms OQ14.Packet05RegionalDivergence.smooth_divergence_on_to_weak
#print axioms OQ14.Packet05RegionalDivergence.regional_partial_commutes_divergence

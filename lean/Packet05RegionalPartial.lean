import Packet05NormalNormal
import Packet05NormalSecond

/-! Local weak L² partials and commutation on open material phases. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalPartial
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.Packet05CurlCommutation
open scoped Topology SchwartzMap

def HasPartialOn (V : Set Space) (u Du : L2Scalar) (i : Fin 3) : Prop :=
  ∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ Du + derivativePair φ i u = 0

theorem global_partial_on (V : Set Space) (u Du : L2Scalar) (i : Fin 3)
    (h : HasWeakPartial u Du i) : HasPartialOn V u Du i := fun φ _ => h φ

theorem cutoff_partial_on (V : Set Space) (τ : Test) (u Du : L2Scalar) (i : Fin 3)
    (hτ : ∀ x ∈ V, τ.function x = 1)
    (h : HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact u) Du i) :
    HasPartialOn V u Du i := by
  apply Packet05LocalDerivative.local_partial_of_ae_eq V u
    (scaleL2 τ.function τ.regular.continuous τ.compact u) Du i h
  filter_upwards [scaleL2_ae τ.function τ.regular.continuous τ.compact u] with x hx hxV
  rw [hx, hτ x hxV, one_mul]

theorem partial_on_of_ae_eq (V : Set Space) (f g D : L2Scalar) (i : Fin 3)
    (hg : HasPartialOn V g D i) (hfg : ∀ᵐ x ∂volume, x ∈ V → f x = g x) :
    HasPartialOn V f D i := by
  intro φ hφV
  have he : derivativePair φ i f = derivativePair φ i g := by
    simp only [derivativePair, testPair_integral]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV]
    · have hnot : x ∉ tsupport φ.function := fun hx => hxV (hφV hx)
      have hz : dcoord φ.function x i = 0 := by simp [dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
      simp [hz]
  rw [he]
  exact hg φ hφV

theorem smooth_partial_on_to_weak (V : Set Space) (hV : IsOpen V) (u v : L2Scalar) (i : Fin 3)
    (h : ∀ φ : Test, ContDiff ℝ 2 φ.function → tsupport φ.function ⊆ V →
      valuePair φ v + derivativePair φ i u = 0) : HasPartialOn V u v i := by
  intro φ hφV
  let ψ : DomainCurl.Test V := ⟨φ, hφV⟩
  obtain ⟨K, f, hK, hKV, hfK, hf, hd⟩ :=
    InteriorTestDensity.interior_test_approximation hV ψ
  let t : ℕ → Test := fun n => ⟨f n, (f n).smooth 1,
    hK.of_isClosed_subset isClosed_closure (hfK n)⟩
  have ht (n : ℕ) : ContDiff ℝ 2 (t n).function := (f n).smooth 2
  have hv (n : ℕ) : scalarProduct v (FourierL2.embed (f n)) +
      scalarProduct u (FourierL2.embed (GradientProjection.pderivative i (f n))) = 0 := by
    have hh := h (t n) (ht n) ((hfK n).trans hKV)
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply, valuePair,
      derivativePair, testPair_integral, t] using hh
  have hlim := ((scalarProduct v).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct u).continuous.tendsto _ |>.comp (hd i))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hv n).symm)))
  simpa only [ψ, testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair] using hz

theorem mixed_partial_on_commute (V : Set Space) (hV : IsOpen V)
    (u Di Dj Vij : L2Scalar) (i j : Fin 3)
    (hi : HasPartialOn V u Di i) (hj : HasPartialOn V u Dj j)
    (hij : HasPartialOn V Di Vij j) : HasPartialOn V Dj Vij i := by
  apply smooth_partial_on_to_weak V hV
  intro φ hφ hφV
  have hs (l : Fin 3) : tsupport (partialTest φ hφ l).function ⊆ V :=
    (RegionalMaxwellHelmholtz.partial_tsupport φ.function l).trans hφV
  have ha := hi (partialTest φ hφ j) (hs j)
  have hb := hj (partialTest φ hφ i) (hs i)
  have hc := hij φ hφV
  have hd := derivativePair_partial_comm φ hφ j i u
  change derivativePair φ j Di + derivativePair (partialTest φ hφ j) i u = 0 at ha
  change derivativePair φ i Dj + derivativePair (partialTest φ hφ i) j u = 0 at hb
  linear_combination hc - ha + hb + hd

end OQ14.Packet05RegionalPartial
#print axioms OQ14.Packet05RegionalPartial.global_partial_on
#print axioms OQ14.Packet05RegionalPartial.cutoff_partial_on
#print axioms OQ14.Packet05RegionalPartial.partial_on_of_ae_eq
#print axioms OQ14.Packet05RegionalPartial.smooth_partial_on_to_weak
#print axioms OQ14.Packet05RegionalPartial.mixed_partial_on_commute

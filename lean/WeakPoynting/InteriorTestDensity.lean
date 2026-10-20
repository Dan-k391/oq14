import WeakPoynting.PartialSmoothing

/-! # Actual compact C1 test approximation with common interior support -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.InteriorTestDensity

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakGreen
  OQ14.PartialSmoothing Filter
open scoped Topology SchwartzMap Manifold

theorem scaleL2_sub (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (u v : L2Scalar) :
    scaleL2 f hf hc (u - v) = scaleL2 f hf hc u - scaleL2 f hf hc v := by
  apply Lp.ext
  filter_upwards [scaleL2_ae f hf hc (u - v), scaleL2_ae f hf hc u,
    scaleL2_ae f hf hc v, Lp.coeFn_sub u v,
    Lp.coeFn_sub (scaleL2 f hf hc u) (scaleL2 f hf hc v)] with x hd hu hv hs ht
  rw [hd, ht]
  simp only [Pi.sub_apply]
  rw [hu, hv, hs]
  simp only [Pi.sub_apply, mul_sub]

theorem scaleL2_norm_le (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (u : L2Scalar) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    ‖scaleL2 f hf hc u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scaleL2_ae f hf hc u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

theorem scaleL2_continuous (f : Space → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Continuous (scaleL2 f hf hc) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf
  let C : NNReal := ⟨max B 0, le_max_right _ _⟩
  have hl : LipschitzWith C (scaleL2 f hf hc) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, dist_eq_norm, ← scaleL2_sub]
    exact scaleL2_norm_le f hf hc (u - v) (fun x => (hB x).trans (le_max_left _ _))
  exact hl.continuous

structure SmoothInterior (Ω : Set Space) extends toDomainTest : DomainCurl.Test Ω where
  smooth : ContDiff ℝ (⊤ : ℕ∞) function

theorem exists_smooth_interior {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ κ : SmoothInterior Ω, ∀ x ∈ K, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  obtain ⟨V, hV, hKV, hVΩ, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨f, hf1, hf0, _⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, Space)) (t := V) hK.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support (fun x => (f x : ℂ)) ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (by simp [hf0 x hn])
  have hts : tsupport (fun x => (f x : ℂ)) ⊆ closure V := closure_mono hs
  have hreg : ContDiff ℝ (⊤ : ℕ∞) (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp f.contMDiff.contDiff
  refine ⟨⟨⟨⟨_, hreg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1),
    hcV.of_isClosed_subset isClosed_closure hts⟩, hts.trans hVΩ⟩, hreg⟩, ?_⟩
  intro x hx
  filter_upwards [hf1.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp only [hy, Complex.ofReal_one]

def cutSchwartz {Ω : Set Space} (κ : SmoothInterior Ω) (f : 𝓢(Space, ℂ)) :
    𝓢(Space, ℂ) :=
  FourierL2.compactSmoothSchwartz (fun x => κ.function x * f x)
    (κ.smooth.mul (f.smooth (⊤ : ℕ∞))) κ.compact.mul_right

theorem cutSchwartz_support {Ω : Set Space} (κ : SmoothInterior Ω)
    (f : 𝓢(Space, ℂ)) :
    tsupport (cutSchwartz κ f : Space → ℂ) ⊆ tsupport κ.function :=
  tsupport_mul_subset_left

theorem embed_cutSchwartz {Ω : Set Space} (κ : SmoothInterior Ω)
    (f : 𝓢(Space, ℂ)) :
    FourierL2.embed (cutSchwartz κ f) =
      scaleL2 κ.function κ.regular.continuous κ.compact (FourierL2.embed f) := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (cutSchwartz κ f),
    scaleL2_ae κ.function κ.regular.continuous κ.compact (FourierL2.embed f),
    FourierL2.embed_ae f] with x hx hy hz
  rw [hx, hy, hz]
  rfl

theorem embed_partial_cutSchwartz {Ω : Set Space} (κ : SmoothInterior Ω)
    (f : 𝓢(Space, ℂ)) (i : Fin 3) :
    FourierL2.embed (GradientProjection.pderivative i (cutSchwartz κ f)) =
      scaleL2 κ.function κ.regular.continuous κ.compact
        (FourierL2.embed (GradientProjection.pderivative i f)) +
      scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
        (κ.compact.fderiv_apply ℝ (basis i)) (FourierL2.embed f) := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (GradientProjection.pderivative i (cutSchwartz κ f)),
    scaleL2_ae κ.function κ.regular.continuous κ.compact
      (FourierL2.embed (GradientProjection.pderivative i f)),
    scaleL2_ae (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
      (κ.compact.fderiv_apply ℝ (basis i)) (FourierL2.embed f),
    FourierL2.embed_ae (GradientProjection.pderivative i f), FourierL2.embed_ae f,
    Lp.coeFn_add
      (scaleL2 κ.function κ.regular.continuous κ.compact
        (FourierL2.embed (GradientProjection.pderivative i f)))
      (scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
        (κ.compact.fderiv_apply ℝ (basis i)) (FourierL2.embed f))]
    with x hx hv hd hdf hf ha
  rw [hx, ha]
  simp only [Pi.add_apply]
  rw [hv, hd, hdf, hf, GradientProjection.pderivative_apply]
  change dcoord (fun y => κ.function y * f y) x i = _
  rw [partial_mul (κ.regular.differentiable le_rfl x) ((f.smooth 1).differentiable le_rfl x)]
  rw [GradientProjection.pderivative_apply]
  ring

theorem interior_test_product {Ω : Set Space} (φ : DomainCurl.Test Ω)
    (κ : SmoothInterior Ω) (hκ : ∀ x ∈ tsupport φ.function, κ.function x = 1) :
    (fun x => κ.function x * φ.function x) = φ.function := by
  funext x
  by_cases hx : x ∈ tsupport φ.function
  · rw [hκ x hx, one_mul]
  · rw [image_eq_zero_of_nmem_tsupport hx, mul_zero]

theorem scale_testL2 {Ω : Set Space} (φ : DomainCurl.Test Ω)
    (κ : SmoothInterior Ω) (hκ : ∀ x ∈ tsupport φ.function, κ.function x = 1) :
    scaleL2 κ.function κ.regular.continuous κ.compact (testL2 φ.toTest) =
      testL2 φ.toTest := by
  apply Lp.ext
  filter_upwards [scaleL2_ae κ.function κ.regular.continuous κ.compact (testL2 φ.toTest),
    continuousL2_ae φ.function φ.regular.continuous φ.compact] with x hx hy
  change testL2 φ.toTest x = φ.function x at hy
  rw [hx, hy]
  exact congrFun (interior_test_product φ κ hκ) x

theorem scale_testDerivativeL2 {Ω : Set Space} (φ : DomainCurl.Test Ω)
    (κ : SmoothInterior Ω) (hκ : ∀ x ∈ tsupport φ.function, κ.function x = 1) (i : Fin 3) :
    scaleL2 κ.function κ.regular.continuous κ.compact (testDerivativeL2 φ.toTest i) +
      scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
        (κ.compact.fderiv_apply ℝ (basis i)) (testL2 φ.toTest) =
      testDerivativeL2 φ.toTest i := by
  apply Lp.ext
  filter_upwards [
    scaleL2_ae κ.function κ.regular.continuous κ.compact (testDerivativeL2 φ.toTest i),
    scaleL2_ae (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
      (κ.compact.fderiv_apply ℝ (basis i)) (testL2 φ.toTest),
    continuousL2_ae φ.function φ.regular.continuous φ.compact,
    continuousL2_ae (fun x => dcoord φ.function x i) (partial_continuous φ.regular i)
      (φ.compact.fderiv_apply ℝ (basis i)),
    Lp.coeFn_add (scaleL2 κ.function κ.regular.continuous κ.compact (testDerivativeL2 φ.toTest i))
      (scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
        (κ.compact.fderiv_apply ℝ (basis i)) (testL2 φ.toTest))]
    with x hv hd hf hdf ha
  change testL2 φ.toTest x = φ.function x at hf
  change testDerivativeL2 φ.toTest i x = dcoord φ.function x i at hdf
  rw [ha]
  simp only [Pi.add_apply]
  rw [hv, hd, hf, hdf]
  have he := congrArg (fun f : Space → ℂ => dcoord f x i) (interior_test_product φ κ hκ)
  change dcoord (fun y => κ.function y * φ.function y) x i = dcoord φ.function x i at he
  rw [partial_mul (κ.regular.differentiable le_rfl x) (φ.regular.differentiable le_rfl x)] at he
  linear_combination he

/-- Actual simultaneous L2 approximation of a compact C1 test and its first
derivatives, with every approximant supported in one fixed compact subset of Ω. -/
theorem interior_test_approximation {Ω : Set Space} (hΩ : IsOpen Ω)
    (φ : DomainCurl.Test Ω) :
    ∃ (K : Set Space) (f : ℕ → 𝓢(Space, ℂ)), IsCompact K ∧ K ⊆ Ω ∧
      (∀ n, tsupport (f n : Space → ℂ) ⊆ K) ∧
      Tendsto (fun n => FourierL2.embed (f n)) atTop (𝓝 (testL2 φ.toTest)) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n)))
        atTop (𝓝 (testDerivativeL2 φ.toTest i)) := by
  obtain ⟨κ, hκ⟩ := exists_smooth_interior hΩ φ.compact φ.inside
  have hκone : ∀ x ∈ tsupport φ.function, κ.function x = 1 :=
    fun x hx => (hκ x hx).self_of_nhds
  obtain ⟨g, hg, hgd⟩ := test_schwartz_approximation φ.toTest
  refine ⟨tsupport κ.function, fun n => cutSchwartz κ (g n), κ.compact, κ.inside,
    fun n => cutSchwartz_support κ (g n), ?_, ?_⟩
  · simp only [embed_cutSchwartz]
    have ht := (scaleL2_continuous κ.function κ.regular.continuous κ.compact).tendsto _ |>.comp hg
    simpa only [scale_testL2 φ κ hκone] using ht
  · intro i
    simp only [embed_partial_cutSchwartz]
    have hv := (scaleL2_continuous κ.function κ.regular.continuous κ.compact).tendsto _ |>.comp (hgd i)
    have hd := (scaleL2_continuous (fun x => dcoord κ.function x i)
      (partial_continuous κ.regular i) (κ.compact.fderiv_apply ℝ (basis i))).tendsto _ |>.comp hg
    simpa only [scale_testDerivativeL2 φ κ hκone i] using hv.add hd

end OQ14.InteriorTestDensity

#print axioms OQ14.InteriorTestDensity.scaleL2_continuous
#print axioms OQ14.InteriorTestDensity.exists_smooth_interior
#print axioms OQ14.InteriorTestDensity.cutSchwartz_support
#print axioms OQ14.InteriorTestDensity.embed_cutSchwartz
#print axioms OQ14.InteriorTestDensity.embed_partial_cutSchwartz
#print axioms OQ14.InteriorTestDensity.scale_testL2
#print axioms OQ14.InteriorTestDensity.scale_testDerivativeL2
#print axioms OQ14.InteriorTestDensity.interior_test_approximation

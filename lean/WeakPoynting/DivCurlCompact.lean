import WeakPoynting.DivCurl

/-! # Actual compact-support weak div-curl approximation -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DivCurlCompact

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurl Filter
open scoped Topology SchwartzMap Convolution

/-- Genuine distributional divergence, against actual compact C1 scalar tests. -/
def HasWeakDivergence (E : L2Vector) (D : L2Scalar) : Prop :=
  ∀ φ : Test, valuePair φ D + derivativePair φ 0 (E 0) +
    derivativePair φ 1 (E 1) + derivativePair φ 2 (E 2) = 0

theorem hasWeakDivergence_integral (E : L2Vector) (D : L2Scalar) :
    HasWeakDivergence E D ↔ ∀ φ : Test,
      (∫ x, D x * φ.function x) + (∫ x, E 0 x * dcoord φ.function x 0) +
        (∫ x, E 1 x * dcoord φ.function x 1) + (∫ x, E 2 x * dcoord φ.function x 2) = 0 := by
  simp only [HasWeakDivergence, valuePair, derivativePair, testPair_integral]

/-- Actual convolution commutes with the genuine distributional divergence. -/
theorem divergence_smoothField (ρ : Test) {E : L2Vector} {D : L2Scalar}
    (h : HasWeakDivergence E D) (x : Space) :
    divergence (smoothField ρ.function E) x = smoothScalar ρ.function D x := by
  have hh := (hasWeakDivergence_integral E D).mp h (shiftedTest ρ x)
  simp only [shiftedTest_partial, mul_neg, integral_neg] at hh
  change dcoord (smoothScalar ρ.function (E 0)) x 0 +
    dcoord (smoothScalar ρ.function (E 1)) x 1 + dcoord (smoothScalar ρ.function (E 2)) x 2 = _
  rw [smoothScalar_partial, smoothScalar_partial, smoothScalar_partial, smoothScalar_integral]
  dsimp only [shiftedTest] at hh
  linear_combination -hh

/-- Compact support belongs to an actual representative, rather than to an
arbitrary choice of values for the L2 equivalence class. -/
def CompactRepresentative (u : L2Scalar) : Prop :=
  ∃ f : Space → ℂ, HasCompactSupport f ∧ (u : Space → ℂ) =ᵐ[volume] f

theorem smoothScalar_compact (ρ : Space → ℂ) (hρ : HasCompactSupport ρ)
    (u : L2Scalar) (hu : CompactRepresentative u) : HasCompactSupport (smoothScalar ρ u) := by
  obtain ⟨f, hf, he⟩ := hu
  have heq : smoothScalar ρ u = convolution f ρ (ContinuousLinearMap.mul ℝ ℂ) volume := by
    funext x
    apply integral_congr_ae
    filter_upwards [he] with y hy
    simp only [ContinuousLinearMap.mul_apply', hy]
  rw [heq]
  exact HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hf hρ

def smoothSchwartz (φ : ContDiffBump (0 : Space)) (u : L2Scalar)
    (hu : CompactRepresentative u) : 𝓢(Space, ℂ) :=
  FourierL2.compactSmoothSchwartz (smoothScalar (complexKernel φ) u)
    (smoothScalar_regular (complexKernel_regular φ) (complexKernel_compact φ) u)
    (smoothScalar_compact _ (complexKernel_compact φ) u hu)

theorem embed_smoothSchwartz (φ : ContDiffBump (0 : Space)) (u : L2Scalar)
    (hu : CompactRepresentative u) : FourierL2.embed (smoothSchwartz φ u hu) = mollifyL2 φ u := by
  apply Lp.ext
  exact (FourierL2.embed_ae (smoothSchwartz φ u hu)).trans
    (smoothScalar_memLp φ u).coeFn_toLp.symm

def smoothSchwartzField (φ : ContDiffBump (0 : Space)) (E : L2Vector)
    (hE : ∀ j, CompactRepresentative (E j)) : Fin 3 → 𝓢(Space, ℂ) :=
  fun j => smoothSchwartz φ (E j) (hE j)

theorem embed_curl_smoothSchwartz (φ : ContDiffBump (0 : Space))
    {E C : L2Vector} (hE : ∀ j, CompactRepresentative (E j)) (hC : HasWeakCurl E C) (j : Fin 3) :
    FourierL2.embed (GradientProjection.curl (smoothSchwartzField φ E hE) j) = mollifyL2 φ (C j) := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (GradientProjection.curl (smoothSchwartzField φ E hE) j),
    (smoothScalar_memLp φ (C j)).coeFn_toLp] with x hx hy
  change mollifyL2 φ (C j) x = smoothScalar (complexKernel φ) (C j) x at hy
  rw [hx, hy, GradientProjection.curl_apply]
  exact congrArg (fun v : Vector => v j) (curl_smoothField (kernelTest φ) hC x)

theorem embed_divergence_smoothSchwartz (φ : ContDiffBump (0 : Space))
    {E : L2Vector} {D : L2Scalar} (hE : ∀ j, CompactRepresentative (E j))
    (hD : HasWeakDivergence E D) :
    FourierL2.embed (GradientProjection.divergence (smoothSchwartzField φ E hE)) = mollifyL2 φ D := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (GradientProjection.divergence (smoothSchwartzField φ E hE)),
    (smoothScalar_memLp φ D).coeFn_toLp] with x hx hy
  change mollifyL2 φ D x = smoothScalar (complexKernel φ) D x at hy
  rw [hx, hy, GradientProjection.divergence_apply]
  exact divergence_smoothField (kernelTest φ) hD x

theorem compact_schwartz_graph_approximation {E C : L2Vector} {D : L2Scalar}
    (hE : ∀ j, CompactRepresentative (E j)) (hC : HasWeakCurl E C) (hD : HasWeakDivergence E D) :
    ∃ f : ℕ → Fin 3 → 𝓢(Space, ℂ),
      (∀ j, Tendsto (fun n => FourierL2.embed (f n j)) atTop (𝓝 (E j))) ∧
      (∀ j, Tendsto (fun n => FourierL2.embed (GradientProjection.curl (f n) j)) atTop (𝓝 (C j))) ∧
      Tendsto (fun n => FourierL2.embed (GradientProjection.divergence (f n))) atTop (𝓝 D) := by
  refine ⟨fun n => smoothSchwartzField (shrinkingBump n) E hE, ?_, ?_, ?_⟩
  · intro j
    simp only [smoothSchwartzField, embed_smoothSchwartz]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (E j)
  · intro j
    simp only [embed_curl_smoothSchwartz _ hE hC]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (C j)
  · simp only [embed_divergence_smoothSchwartz _ hE hD]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto D

/-- An actual weak coordinate derivative, defined by the integral test identity. -/
def HasWeakPartial (u v : L2Scalar) (i : Fin 3) : Prop :=
  ∀ φ : Test, valuePair φ v + derivativePair φ i u = 0

theorem schwartz_hasWeakPartial (f : 𝓢(Space, ℂ)) (i : Fin 3) :
    HasWeakPartial (FourierL2.embed f) (FourierL2.embed (GradientProjection.pderivative i f)) i := by
  intro φ
  simp only [valuePair, derivativePair, testPair_integral]
  have h0 : (∫ x, FourierL2.embed (GradientProjection.pderivative i f) x * φ.function x) =
      ∫ x, dcoord f x i * φ.function x := by
    apply integral_congr_ae
    filter_upwards [FourierL2.embed_ae (GradientProjection.pderivative i f)] with x hx
    rw [hx, GradientProjection.pderivative_apply]
  have h1 : (∫ x, FourierL2.embed f x * dcoord φ.function x i) =
      ∫ x, f x * dcoord φ.function x i := by
    apply integral_congr_ae
    filter_upwards [FourierL2.embed_ae f] with x hx
    rw [hx]
  rw [h0, h1, partial_integration_by_parts (f.smooth 1) φ.regular φ.compact i]
  ring

theorem weakPartial_limit {u v : L2Scalar} {us vs : ℕ → L2Scalar} (i : Fin 3)
    (hu : Tendsto us atTop (𝓝 u)) (hv : Tendsto vs atTop (𝓝 v))
    (h : ∀ n, HasWeakPartial (us n) (vs n) i) : HasWeakPartial u v i := by
  intro φ
  have hl := ((valuePair φ).continuous.tendsto v |>.comp hv).add
    ((derivativePair φ i).continuous.tendsto u |>.comp hu)
  exact tendsto_nhds_unique hl
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (h n φ).symm)))

end OQ14.DivCurlCompact

#print axioms OQ14.DivCurlCompact.divergence_smoothField
#print axioms OQ14.DivCurlCompact.smoothScalar_compact
#print axioms OQ14.DivCurlCompact.embed_curl_smoothSchwartz
#print axioms OQ14.DivCurlCompact.embed_divergence_smoothSchwartz
#print axioms OQ14.DivCurlCompact.compact_schwartz_graph_approximation
#print axioms OQ14.DivCurlCompact.schwartz_hasWeakPartial
#print axioms OQ14.DivCurlCompact.weakPartial_limit

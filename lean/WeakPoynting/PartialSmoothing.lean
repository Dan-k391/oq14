import WeakPoynting.DivCurlRegularity

/-! # Genuine scalar weak-derivative smoothing and compact C1 test density -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.PartialSmoothing

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.WeakGreen Filter
open scoped Topology SchwartzMap

def continuousL2 (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) : L2Scalar :=
  (hf.memLp_of_hasCompactSupport hc).toLp f

theorem continuousL2_ae (f : Space → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    continuousL2 f hf hc =ᵐ[volume] f :=
  (hf.memLp_of_hasCompactSupport hc).coeFn_toLp

def testL2 (φ : Test) : L2Scalar := continuousL2 φ.function φ.regular.continuous φ.compact

def testDerivativeL2 (φ : Test) (i : Fin 3) : L2Scalar :=
  continuousL2 (fun x => dcoord φ.function x i) (partial_continuous φ.regular i)
    (φ.compact.fderiv_apply ℝ (basis i))

theorem testL2_hasWeakPartial (φ : Test) (i : Fin 3) :
    HasWeakPartial (testL2 φ) (testDerivativeL2 φ i) i := by
  intro ψ
  simp only [valuePair, derivativePair, testPair_integral]
  have h0 : (∫ x, testDerivativeL2 φ i x * ψ.function x) =
      ∫ x, dcoord φ.function x i * ψ.function x := by
    apply integral_congr_ae
    filter_upwards [continuousL2_ae _ (partial_continuous φ.regular i)
      (φ.compact.fderiv_apply ℝ (basis i))] with x hx
    rw [show testDerivativeL2 φ i x = dcoord φ.function x i from hx]
  have h1 : (∫ x, testL2 φ x * dcoord ψ.function x i) =
      ∫ x, φ.function x * dcoord ψ.function x i := by
    apply integral_congr_ae
    filter_upwards [continuousL2_ae φ.function φ.regular.continuous φ.compact] with x hx
    rw [show testL2 φ x = φ.function x from hx]
  rw [h0, h1, partial_integration_by_parts φ.regular ψ.regular ψ.compact i]
  ring

theorem smoothScalar_weakPartial (ρ : Test) {u v : L2Scalar} {i : Fin 3}
    (h : HasWeakPartial u v i) (x : Space) :
    dcoord (smoothScalar ρ.function u) x i = smoothScalar ρ.function v x := by
  have hh := h (shiftedTest ρ x)
  simp only [valuePair, derivativePair, testPair_integral, shiftedTest_partial,
    mul_neg, integral_neg] at hh
  rw [smoothScalar_partial, smoothScalar_integral]
  dsimp only [shiftedTest] at hh
  linear_combination -hh

theorem embed_partial_smoothSchwartz (φ : ContDiffBump (0 : Space))
    {u v : L2Scalar} (hu : CompactRepresentative u) {i : Fin 3}
    (h : HasWeakPartial u v i) :
    FourierL2.embed (GradientProjection.pderivative i (smoothSchwartz φ u hu)) =
      mollifyL2 φ v := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (GradientProjection.pderivative i (smoothSchwartz φ u hu)),
    (smoothScalar_memLp φ v).coeFn_toLp] with x hx hy
  change mollifyL2 φ v x = smoothScalar (complexKernel φ) v x at hy
  rw [hx, hy, GradientProjection.pderivative_apply]
  exact smoothScalar_weakPartial (kernelTest φ) h x

/-- The scalar field and its genuine weak derivatives are approximated
simultaneously by the same compact smooth convolutions. -/
theorem compact_partial_graph_approximation {u : L2Scalar} {D : Fin 3 → L2Scalar}
    (hu : CompactRepresentative u) (hD : ∀ i, HasWeakPartial u (D i) i) :
    ∃ f : ℕ → 𝓢(Space, ℂ),
      Tendsto (fun n => FourierL2.embed (f n)) atTop (𝓝 u) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n)))
        atTop (𝓝 (D i)) := by
  refine ⟨fun n => smoothSchwartz (shrinkingBump n) u hu, ?_, ?_⟩
  · simp only [embed_smoothSchwartz]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto u
  · intro i
    simp only [embed_partial_smoothSchwartz _ hu (hD i)]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (D i)

theorem test_schwartz_approximation (φ : Test) :
    ∃ f : ℕ → 𝓢(Space, ℂ),
      Tendsto (fun n => FourierL2.embed (f n)) atTop (𝓝 (testL2 φ)) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n)))
        atTop (𝓝 (testDerivativeL2 φ i)) :=
  compact_partial_graph_approximation
    ⟨φ.function, φ.compact, continuousL2_ae φ.function φ.regular.continuous φ.compact⟩
    (testL2_hasWeakPartial φ)

theorem scalarProduct_continuousL2 (u : L2Scalar) (f : Space → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    scalarProduct u (continuousL2 f hf hc) = testPair f hf hc u := by
  rw [scalarProduct_integral, testPair_integral]
  apply integral_congr_ae
  filter_upwards [continuousL2_ae f hf hc] with x hx
  rw [hx]

theorem scalarProduct_embed (u : L2Scalar) (f : 𝓢(Space, ℂ)) :
    scalarProduct u (FourierL2.embed f) = ∫ x, u x * f x := by
  rw [scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [FourierL2.embed_ae f] with x hx
  rw [hx]

/-- An actual identity against all Schwartz functions extends to every compact
C1 test through the proved value-and-derivative L2 approximation. -/
theorem hasWeakPartial_of_schwartz_integral {u v : L2Scalar} (i : Fin 3)
    (h : ∀ f : 𝓢(Space, ℂ),
      (∫ x, v x * f x) + (∫ x, u x * dcoord f x i) = 0) :
    HasWeakPartial u v i := by
  intro φ
  obtain ⟨f, hf, hd⟩ := test_schwartz_approximation φ
  have hl := ((scalarProduct v).continuous.tendsto _ |>.comp hf).add
    ((scalarProduct u).continuous.tendsto _ |>.comp (hd i))
  have hz (n : ℕ) :
      scalarProduct v (FourierL2.embed (f n)) +
        scalarProduct u (FourierL2.embed (GradientProjection.pderivative i (f n))) = 0 := by
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply] using h (f n)
  have he := tendsto_nhds_unique hl
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hz n).symm)))
  simpa only [testL2, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair]
    using he

theorem hasWeakCurl_of_schwartz_integral {E C : L2Vector}
    (h : ∀ (f : 𝓢(Space, ℂ)) (j : Fin 3),
      (∫ x, C j x * f x) =
        (∫ x, E (next j) x * dcoord f x (previous j)) -
        (∫ x, E (previous j) x * dcoord f x (next j))) :
    HasWeakCurl E C := by
  rw [hasWeakCurl_iff_integral]
  intro φ j
  obtain ⟨f, hf, hd⟩ := test_schwartz_approximation φ
  have hl := (scalarProduct (C j)).continuous.tendsto _ |>.comp hf
  have hr := ((scalarProduct (E (next j))).continuous.tendsto _ |>.comp (hd (previous j))).sub
    ((scalarProduct (E (previous j))).continuous.tendsto _ |>.comp (hd (next j)))
  have hz (n : ℕ) :
      scalarProduct (C j) (FourierL2.embed (f n)) =
        scalarProduct (E (next j))
          (FourierL2.embed (GradientProjection.pderivative (previous j) (f n))) -
        scalarProduct (E (previous j))
          (FourierL2.embed (GradientProjection.pderivative (next j) (f n))) := by
    simpa only [scalarProduct_embed, GradientProjection.pderivative_apply] using h (f n) j
  have he := tendsto_nhds_unique hl
    (hr.congr' (Eventually.of_forall (fun n => (hz n).symm)))
  simpa only [testL2, testDerivativeL2, scalarProduct_continuousL2, testPair_integral] using he

end OQ14.PartialSmoothing

#print axioms OQ14.PartialSmoothing.testL2_hasWeakPartial
#print axioms OQ14.PartialSmoothing.smoothScalar_weakPartial
#print axioms OQ14.PartialSmoothing.embed_partial_smoothSchwartz
#print axioms OQ14.PartialSmoothing.compact_partial_graph_approximation
#print axioms OQ14.PartialSmoothing.test_schwartz_approximation
#print axioms OQ14.PartialSmoothing.scalarProduct_continuousL2
#print axioms OQ14.PartialSmoothing.scalarProduct_embed
#print axioms OQ14.PartialSmoothing.hasWeakPartial_of_schwartz_integral
#print axioms OQ14.PartialSmoothing.hasWeakCurl_of_schwartz_integral

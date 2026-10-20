import WeakPoynting.DivCurlRegularity

/-! # Local magnetic weak L2 derivatives from actual Maxwell equations

The divergence-of-curl identity is tested against compact C2 functions. Smooth
convolutions and C2 interior cutoffs preserve that test class; no unproved
upgrade to C1 distribution tests is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.LocalRegularity

open MeasureTheory OQ14.Maxwell OQ14.WeakPoynting OQ14.DivCurlCompact
  OQ14.DivCurlRegularity OQ14.CurlCutoff Filter
open scoped Topology SchwartzMap Manifold

def HasSmoothWeakDivergence (E : WeakCurl.L2Vector) (D : WeakCurl.L2Scalar) : Prop :=
  ∀ φ : WeakCurl.Test, ContDiff ℝ 2 φ.function →
    WeakCurl.valuePair φ D + WeakCurl.derivativePair φ 0 (E 0) +
      WeakCurl.derivativePair φ 1 (E 1) + WeakCurl.derivativePair φ 2 (E 2) = 0

theorem divergence_smooth_kernel (φ : ContDiffBump (0 : Space))
    {E : WeakCurl.L2Vector} {D : WeakCurl.L2Scalar}
    (h : HasSmoothWeakDivergence E D) (x : Space) :
    divergence (smoothField (complexKernel φ) E) x = smoothScalar (complexKernel φ) D x := by
  have hr : ContDiff ℝ 2 (shiftedTest (kernelTest φ) x).function :=
    ((complexKernel_regular φ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp
      (contDiff_const.sub contDiff_id)
  have hh := h (shiftedTest (kernelTest φ) x) hr
  simp only [WeakCurl.valuePair, WeakCurl.derivativePair, WeakCurl.testPair_integral,
    shiftedTest_partial, mul_neg, integral_neg] at hh
  change dcoord (smoothScalar (kernelTest φ).function (E 0)) x 0 +
    dcoord (smoothScalar (kernelTest φ).function (E 1)) x 1 +
      dcoord (smoothScalar (kernelTest φ).function (E 2)) x 2 = _
  rw [smoothScalar_partial, smoothScalar_partial, smoothScalar_partial, smoothScalar_integral]
  dsimp only [shiftedTest, kernelTest] at hh ⊢
  linear_combination -hh

theorem embed_divergence_smooth_kernel (φ : ContDiffBump (0 : Space))
    {E : WeakCurl.L2Vector} {D : WeakCurl.L2Scalar}
    (hE : ∀ j, CompactRepresentative (E j)) (hD : HasSmoothWeakDivergence E D) :
    FourierL2.embed (GradientProjection.divergence (smoothSchwartzField φ E hE)) =
      mollifyL2 φ D := by
  apply Lp.ext
  filter_upwards [FourierL2.embed_ae (GradientProjection.divergence (smoothSchwartzField φ E hE)),
    (smoothScalar_memLp φ D).coeFn_toLp] with x hx hy
  change mollifyL2 φ D x = smoothScalar (complexKernel φ) D x at hy
  rw [hx, hy, GradientProjection.divergence_apply]
  exact divergence_smooth_kernel φ hD x

/-- Compact C2 divergence tests already suffice for the actual weak derivative
construction, since the explicit convolution kernels are smooth. -/
theorem compact_smooth_divcurl_regularity {E C : WeakCurl.L2Vector}
    {D : WeakCurl.L2Scalar} (hE : ∀ j, CompactRepresentative (E j))
    (hC : WeakCurl.HasWeakCurl E C) (hD : HasSmoothWeakDivergence E D) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial (E p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) = (∑ j, ‖C j‖ ^ 2) + ‖D‖ ^ 2 := by
  apply weak_derivatives_of_approximation (fun n => smoothSchwartzField (shrinkingBump n) E hE)
  · intro j
    simp only [smoothSchwartzField, embed_smoothSchwartz]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (E j)
  · intro j
    simp only [curlL2, embed_curl_smoothSchwartz _ hE hC]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto (C j)
  · simp only [divL2, embed_divergence_smooth_kernel _ hE hD]
    exact mollifyL2_tendsto shrinkingBump shrinkingBump_tendsto D

theorem maxwell_magnetic_divergence {Ω : Set Space} (ω : ℝ) (hω : ω ≠ 0)
    (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell ω (fun _ => 1) ε E H) :
    DomainCurl.DivergenceFree Ω H.val.1 := by
  intro f hf hc hi
  have hh := DomainCurl.weak_divergence_curl Ω E.property f hf hc hi
  have he (j : Fin 3) :
      (∫ x in Ω, E.val.2 j x * dcoord f x j) =
        (Complex.I * ω) * (∫ x in Ω, H.val.1 j x * dcoord f x j) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hM.1] with x hx
    rw [hx j]
    simp only [Complex.ofReal_one, mul_one]
    ring
  rw [he 0, he 1, he 2] at hh
  have hn : Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  apply (mul_eq_zero.mp ?_).resolve_left hn
  linear_combination hh

def cutoffDivergence (Ω : Set Space) (χ : WeakCurl.Test)
    (E : DomainCurl.L2Vector Ω) : DomainCurl.L2Scalar Ω :=
  derivativeMultiply Ω χ 0 (E 0) + derivativeMultiply Ω χ 1 (E 1) +
    derivativeMultiply Ω χ 2 (E 2)

theorem cutoff_extend_compact {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (E : DomainCurl.L2Vector Ω) (j : Fin 3) :
    CompactRepresentative (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E) j) := by
  refine ⟨fun x => χ.function x * Ω.indicator (E j) x, χ.compact.mul_right, ?_⟩
  have hm := (ae_restrict_iff' hΩ.measurableSet).mp
    (mulL2_ae Ω χ.function χ.regular.continuous χ.compact (E j))
  filter_upwards [extendScalar_ae Ω hΩ.measurableSet (multiply Ω χ.toTest E j), hm]
    with x he hx
  change extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest E j) x = _
  rw [he]
  by_cases hn : x ∈ Ω
  · simpa only [Set.indicator_of_mem hn] using hx hn
  · simp [hn]

/-- The divergence product rule is derived by testing the regional divergence
equation with the literal product χφ. -/
theorem divergence_cutoff_extend {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    {E : DomainCurl.L2Vector Ω} (hE : DomainCurl.DivergenceFree Ω E) :
    HasSmoothWeakDivergence
      (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E))
      (extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest E)) := by
  intro φ hφ
  have hh := hE (fun x => χ.function x * φ.function x) (hχ.mul hφ)
    χ.compact.mul_right (tsupport_mul_subset_left.trans χ.inside)
  have hp (i : Fin 3) := derivative_pairing_product Ω χ.toTest φ i (E i)
  simp only [DomainCurl.testPair_integral] at hp
  rw [hp 0, hp 1, hp 2] at hh
  simp only [WeakCurl.valuePair, WeakCurl.derivativePair, extendVector, extendScalar_pair,
    cutoffDivergence, map_add, DomainCurl.testPair_integral, multiply,
    DomainCurl.regionMeasure] at hh ⊢
  linear_combination hh

theorem cutoff_divcurl_regularity {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (E : DomainCurl.HCurl Ω) (hD : DomainCurl.DivergenceFree Ω E.val.1) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) =
        (∑ j, ‖extendVector Ω hΩ.measurableSet
          (productCurl Ω χ.toTest E.val.1 E.val.2) j‖ ^ 2) +
        ‖extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest E.val.1)‖ ^ 2 := by
  exact compact_smooth_divcurl_regularity (cutoff_extend_compact hΩ χ E.val.1)
    (weakCurl_cutoff_extend Ω hΩ χ E.property) (divergence_cutoff_extend hΩ χ hχ hD)

/-- Actual regional weak Maxwell equations yield all nine weak L2 derivatives
of every interior C2 cutoff of H, with an exact energy identity. -/
theorem maxwell_cutoff_magnetic_regularity {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell ω (fun _ => 1) ε E H) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) =
        (∑ j, ‖extendVector Ω hΩ.measurableSet
          (productCurl Ω χ.toTest H.val.1 H.val.2) j‖ ^ 2) +
        ‖extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest H.val.1)‖ ^ 2 :=
  cutoff_divcurl_regularity hΩ χ hχ H (maxwell_magnetic_divergence ω hω ε E H hM)

theorem exists_c2_interior_cutoff {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : DomainCurl.Test Ω, ContDiff ℝ 2 χ.function ∧
      ∀ x ∈ K, χ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  obtain ⟨V, hV, hKV, hVΩ, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨f, hf1, hf0, _⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, Space)) (t := V) hK.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support (fun x => (f x : ℂ)) ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (by simp [hf0 x hn])
  have hts : tsupport (fun x => (f x : ℂ)) ⊆ closure V := closure_mono hs
  have hreg : ContDiff ℝ 2 (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (f.contMDiff.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  refine ⟨⟨⟨_, hreg.of_le (by norm_num), hcV.of_isClosed_subset isClosed_closure hts⟩,
    hts.trans hVΩ⟩, hreg, ?_⟩
  intro x hx
  have he := hf1.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [he] with y hy
  simp only [hy, Complex.ofReal_one]

/-- Explicit local H1 regularity: near every compact interior set, H agrees
almost everywhere with an actual global L2 field having nine actual weak L2
derivatives. Neither H nor E must be globally square integrable. -/
theorem maxwell_magnetic_local_h1 {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell ω (fun _ => 1) ε E H) :
    ∃ (U : Set Space) (F : WeakCurl.L2Vector) (G : DerivativeIndex → WeakCurl.L2Scalar),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      (∀ p, HasWeakPartial (F p.2) (G p) p.1) ∧
      (∀ j, (fun x => F j x) =ᵐ[volume.restrict U] (fun x => H.val.1 j x)) := by
  obtain ⟨χ, hχ, hχK⟩ := exists_c2_interior_cutoff hΩ hK hKΩ
  obtain ⟨G, hG, _⟩ := maxwell_cutoff_magnetic_regularity hΩ χ hχ ω hω ε E H hM
  let U := interior {x | χ.function x = 1} ∩ Ω
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have hUΩ : U ⊆ Ω := Set.inter_subset_right
  have hKU : K ⊆ U := by
    intro x hx
    exact ⟨mem_interior_iff_mem_nhds.mpr (hχK x hx), hKΩ hx⟩
  refine ⟨U, extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1),
    G, hU, hKU, hUΩ, hG, ?_⟩
  intro j
  have hh := (ae_restrict_iff' hΩ.measurableSet).mp
    (LocalPower.cutExtend_field_ae hΩ χ H j)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hh] with x hx
  intro hxu
  have hχx : χ.function x = 1 :=
    (show interior {y | χ.function y = 1} ⊆ {y | χ.function y = 1} from interior_subset) hxu.1
  change (LocalPower.cutExtend hΩ χ H).val.1 j x = H.val.1 j x
  rw [hx (hUΩ hxu), hχx, one_mul]

end OQ14.LocalRegularity

#print axioms OQ14.LocalRegularity.divergence_smooth_kernel
#print axioms OQ14.LocalRegularity.compact_smooth_divcurl_regularity
#print axioms OQ14.LocalRegularity.maxwell_magnetic_divergence
#print axioms OQ14.LocalRegularity.cutoff_extend_compact
#print axioms OQ14.LocalRegularity.divergence_cutoff_extend
#print axioms OQ14.LocalRegularity.cutoff_divcurl_regularity
#print axioms OQ14.LocalRegularity.maxwell_cutoff_magnetic_regularity
#print axioms OQ14.LocalRegularity.exists_c2_interior_cutoff
#print axioms OQ14.LocalRegularity.maxwell_magnetic_local_h1

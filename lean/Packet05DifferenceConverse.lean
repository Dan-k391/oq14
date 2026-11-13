import MaxwellWeakTranslation
import WeakPoynting.Translations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import WeakPoynting.Poynting

/-! The distributional derivative is the test-pairing limit of actual L2
difference quotients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferenceConverse
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.WeakTranslations OQ14.MaxwellDifferenceQuotient OQ14.WeakPower
  OQ14.DivCurlCompact
open scoped Topology ComplexConjugate

theorem quotient_pair_tendsto (u : L2Scalar) (i : Fin 3) (φ : Test) :
    Tendsto (fun h : ℝ => valuePair φ (quotient u i h)) (𝓝[≠] 0)
      (𝓝 (-derivativePair φ i u)) := by
  let F : Space → ℂ := smoothScalar (shiftedTest φ 0).function u
  have hreg : ContDiff ℝ 1 F := smoothScalar_regular (shiftedTest φ 0).regular
    (shiftedTest φ 0).compact u
  have hd : HasDerivAt (fun h : ℝ => F (h • basis i)) (dcoord F 0 i) 0 := by
    have hi : HasDerivAt (fun h : ℝ => h • basis i) (basis i) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (basis i)
    have hF : HasFDerivAt F (fderiv ℝ F 0) ((0 : ℝ) • basis i) := by
      simpa using (hreg.differentiable le_rfl 0).hasFDerivAt
    have hc := HasFDerivAt.comp_hasDerivAt (0 : ℝ) hF hi
    simpa [F, dcoord] using hc
  have hderiv : dcoord F 0 i = -derivativePair φ i u := by
    rw [show dcoord F 0 i = dcoord (smoothScalar (shiftedTest φ 0).function u) 0 i from rfl,
      smoothScalar_partial, derivativePair, testPair_integral, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [shiftedTest_partial]
    simp only [zero_sub, neg_neg, mul_neg]
  rw [← hderiv]
  have ht := hasDerivAt_iff_tendsto_slope.mp hd
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hpair : valuePair φ (quotient u i h) =
      (h : ℂ)⁻¹ * (F (h • basis i) - F 0) := by
    change valuePair φ (((h : ℂ)⁻¹) • (translateL2 u (h • basis i) - u)) = _
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [valuePair_translate, show valuePair φ u = F 0 from by
      simpa [F, translateL2_zero] using (valuePair_translate φ u 0)]
  rw [hpair]
  simp [slope, smul_eq_mul]

/-- A uniform local difference-quotient bound yields an actual L² weak
partial derivative, by weak-star compactness and Hilbert-space Riesz. -/
theorem weakPartial_of_bounded_quotients (u : L2Scalar) (i : Fin 3)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ → ‖quotient u i h‖ ≤ B) :
    ∃ v : L2Scalar, HasWeakPartial u v i ∧ ‖v‖ ≤ B := by
  let q : ℝ → WeakDual ℂ L2Scalar := fun h =>
    NormedSpace.Dual.toWeakDual (scalarProduct (quotient u i h))
  let K : Set (WeakDual ℂ L2Scalar) :=
    WeakDual.toNormedDual ⁻¹' Metric.closedBall (0 : NormedSpace.Dual ℂ L2Scalar) B
  have hK : IsCompact K := WeakDual.isCompact_closedBall _ _ _
  have hmem : ∀ᶠ h in 𝓝[≠] (0 : ℝ), q h ∈ K := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδ),
      self_mem_nhdsWithin] with h hh hne
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have hn : h ≠ 0 := by simpa using hne
    simp only [K, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      q, WeakDual.coe_toNormedDual, NormedSpace.Dual.coe_toWeakDual]
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro y
    exact (scalarProduct_norm_le _ _).trans
      (mul_le_mul_of_nonneg_right (hbound h hn hh') (norm_nonneg y))
  have hmap : map q (𝓝[≠] (0 : ℝ)) ≤ 𝓟 K := le_principal_iff.mpr hmem
  obtain ⟨F, hFK, hcluster⟩ := hK.exists_clusterPt hmap
  let p : L2Scalar := (InnerProductSpace.toDual ℂ L2Scalar).symm (WeakDual.toNormedDual F)
  let v : L2Scalar := conjScalar p
  have hconj : conjScalar v = p := by
    apply Lp.ext
    filter_upwards [conjScalar_ae v, conjScalar_ae p] with x hv hp
    change conjScalar v x = p x
    rw [hv]
    change conj (conjScalar p x) = p x
    rw [hp]
    simp
  have hvnorm : ‖v‖ ≤ B := by
    have hc : ‖v‖ ≤ ‖p‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [conjScalar_ae p] with x hx
      change ‖conjScalar p x‖ ≤ ‖p x‖
      rw [hx]
      simp
    have hp : ‖p‖ = ‖WeakDual.toNormedDual F‖ :=
      (InnerProductSpace.toDual ℂ L2Scalar).symm.norm_map _
    have hF : ‖WeakDual.toNormedDual F‖ ≤ B := by
      simpa only [K, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hFK
    exact hc.trans (hp.le.trans hF)
  refine ⟨v, ?_, hvnorm⟩
  intro φ
  have heval : (WeakDual.toNormedDual F) (PartialSmoothing.testL2 φ) =
      -derivativePair φ i u := by
    let l := 𝓝 F ⊓ map q (𝓝[≠] (0 : ℝ))
    haveI : NeBot l := hcluster
    have hleft : Tendsto (fun z : WeakDual ℂ L2Scalar => z (PartialSmoothing.testL2 φ)) l
        (𝓝 (F (PartialSmoothing.testL2 φ))) :=
      (WeakDual.eval_continuous (PartialSmoothing.testL2 φ)).continuousAt.tendsto.mono_left inf_le_left
    have ht := quotient_pair_tendsto u i φ
    have hright : Tendsto (fun z : WeakDual ℂ L2Scalar => z (PartialSmoothing.testL2 φ)) l
        (𝓝 (-derivativePair φ i u)) := by
      apply (show Tendsto (fun z : WeakDual ℂ L2Scalar => z (PartialSmoothing.testL2 φ))
        (map q (𝓝[≠] (0 : ℝ))) (𝓝 (-derivativePair φ i u)) from ?_).mono_left inf_le_right
      rw [Filter.tendsto_map'_iff]
      change Tendsto (fun h : ℝ => scalarProduct (quotient u i h) (PartialSmoothing.testL2 φ)) _ _
      simpa only [PartialSmoothing.testL2, PartialSmoothing.scalarProduct_continuousL2,
        valuePair] using ht
    exact tendsto_nhds_unique hleft hright
  have hp : scalarProduct v (PartialSmoothing.testL2 φ) =
      (WeakDual.toNormedDual F) (PartialSmoothing.testL2 φ) := by
    rw [scalarProduct, innerSL_apply]
    change inner (𝕜 := ℂ) (conjScalar v) (PartialSmoothing.testL2 φ) = _
    rw [hconj]
    exact InnerProductSpace.toDual_symm_apply
  have he : valuePair φ v = -derivativePair φ i u := by
    rw [← heval, ← hp]
    exact (PartialSmoothing.scalarProduct_continuousL2 v φ.function φ.regular.continuous φ.compact).symm
  change valuePair φ v + derivativePair φ i u = 0
  rw [he, neg_add_cancel]

end OQ14.Packet05DifferenceConverse
#print axioms OQ14.Packet05DifferenceConverse.quotient_pair_tendsto
#print axioms OQ14.Packet05DifferenceConverse.weakPartial_of_bounded_quotients

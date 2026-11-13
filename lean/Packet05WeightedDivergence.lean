import Packet05FlatWeight
import Packet05DivergenceUpgrade
import Packet05DifferenceMaxwell

/-! The weighted electric cutoff has a genuine L² divergence, obtained from
the actual Maxwell curl of H without differentiating the jump coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05WeightedDivergence
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.CurlCutoff OQ14.DivCurlCompact OQ14.LocalRegularity
  OQ14.Packet05FlatWeight OQ14.Packet05DivergenceUpgrade
open scoped Topology

theorem cutoff_divergence_vanishes_on {Ω U : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hUΩ : U ⊆ Ω)
    (hχ : ∀ x ∈ U, χ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (V : DomainCurl.L2Vector Ω) :
    ∀ᵐ x ∂volume, x ∈ U →
      extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest V) x = 0 := by
  have he := (ae_restrict_iff' hΩ.measurableSet).mp
    (LocalPower.extendScalar_ae_region hΩ.measurableSet (cutoffDivergence Ω χ.toTest V))
  have hs := (ae_restrict_iff' hΩ.measurableSet).mp
    (Lp.coeFn_add (derivativeMultiply Ω χ.toTest 0 (V 0) + derivativeMultiply Ω χ.toTest 1 (V 1))
      (derivativeMultiply Ω χ.toTest 2 (V 2)))
  have ha := (ae_restrict_iff' hΩ.measurableSet).mp
    (Lp.coeFn_add (derivativeMultiply Ω χ.toTest 0 (V 0)) (derivativeMultiply Ω χ.toTest 1 (V 1)))
  have hm (j : Fin 3) := (ae_restrict_iff' hΩ.measurableSet).mp
    (mulL2_ae Ω (fun x => dcoord χ.function x j) (partial_continuous χ.regular j)
      (χ.compact.fderiv_apply ℝ (basis j)) (V j))
  filter_upwards [he, hs, ha, hm 0, hm 1, hm 2] with x he hs ha h0 h1 h2 hx
  have hxΩ := hUΩ hx
  have hdχ (j : Fin 3) : dcoord χ.function x j = 0 := by
    simp [dcoord, (hχ x hx).fderiv_eq]
  rw [he hxΩ]
  change ((derivativeMultiply Ω χ.toTest 0 (V 0) + derivativeMultiply Ω χ.toTest 1 (V 1) +
    derivativeMultiply Ω χ.toTest 2 (V 2) : DomainCurl.L2Scalar Ω) : Space → ℂ) x = 0
  rw [hs hxΩ]
  simp only [Pi.add_apply]
  rw [ha hxΩ]
  simp only [Pi.add_apply]
  change mulL2 Ω (fun x => dcoord χ.function x 0) _ _ (V 0) x +
    mulL2 Ω (fun x => dcoord χ.function x 1) _ _ (V 1) x +
    mulL2 Ω (fun x => dcoord χ.function x 2) _ _ (V 2) x = 0
  rw [h0 hxΩ, h1 hxΩ, h2 hxΩ, hdχ, hdχ, hdχ]
  simp

theorem actual_cutoff_weighted_divergence {Ω S : Set Space}
    (hΩ : IsOpen Ω) (κ χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (hχS : tsupport χ.function ⊆ S) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H) :
    ∃ D : L2Scalar, HasWeakDivergence
      (fun j => mulWeight d hd
        (scaleL2 χ.function χ.regular.continuous χ.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 j))) D ∧
      D = (-(Complex.I * (k : ℂ)))⁻¹ •
        extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest H.val.2) := by
  let c : ℂ := -(Complex.I * (k : ℂ))
  have hc : c ≠ 0 := neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk))
  let P : L2Vector := extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2)
  let W : L2Vector := fun j => mulWeight d hd
    (scaleL2 χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j))
  let D : L2Scalar := extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest H.val.2)
  have hdiv : DomainCurl.DivergenceFree Ω H.val.2 := by
    intro f hf hfcomp hfin
    exact DomainCurl.weak_divergence_curl Ω H.property f hf hfcomp hfin
  have hpdiv : HasWeakDivergence P D := smooth_divergence_to_weak P D
    (divergence_cutoff_extend hΩ χ hχ hdiv)
  have hpw : ∀ j, P j = c • W j := by
    intro j
    apply Lp.ext
    have hp := extendScalar_ae Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2 j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp
      (mulL2_ae Ω χ.function χ.regular.continuous χ.compact (H.val.2 j))
    have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ E j)
    have hmax := (ae_restrict_iff' hΩ.measurableSet).mp hM.2
    filter_upwards [hp, hm, he, hmax, mulWeight_ae d hd
      (scaleL2 χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)),
      scaleL2_ae χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j),
      Lp.coeFn_smul c (W j)] with x hp hm he hmax hw hs hsm
    change extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2 j) x = _
    rw [hp, hsm]
    change Ω.indicator (multiply Ω χ.toTest H.val.2 j) x = c * W j x
    change W j x = weight d x * _ at hw
    rw [hw, hs]
    by_cases hx : x ∈ tsupport χ.function
    · have hxS := hχS hx
      have hxΩ := hSΩ hxS
      have hκx : κ.function x = 1 := (hκ x hxS).self_of_nhds
      rw [Set.indicator_of_mem hxΩ]
      change mulL2 Ω χ.function χ.regular.continuous χ.compact (H.val.2 j) x = _
      rw [hm hxΩ, he hxΩ, hκx]
      simp only [one_mul]
      rw [hmax hxΩ j]
      simp only [weight, c]
      ring
    · have hz : χ.function x = 0 := image_eq_zero_of_nmem_tsupport hx
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
        change mulL2 Ω χ.function χ.regular.continuous χ.compact (H.val.2 j) x = _
        rw [hm hxΩ, hz]
        simp
      · simp [hxΩ, hz]
  refine ⟨c⁻¹ • D, ?_, rfl⟩
  intro φ
  have h := hpdiv φ
  simp only [hpw, map_smul, smul_eq_mul] at h ⊢
  have hi : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hh := congrArg (fun z : ℂ => c⁻¹ * z) h
  simp only [mul_zero] at hh
  calc
    _ = c⁻¹ * (valuePair φ D + c * derivativePair φ 0 (W 0) +
        c * derivativePair φ 1 (W 1) + c * derivativePair φ 2 (W 2)) := by
      rw [mul_add, mul_add, mul_add]
      simp only [← mul_assoc, hi, one_mul]
      rfl
    _ = 0 := hh


theorem complex_cutoff_weighted_divergence {Ω S : Set Space}
    (hΩ : IsOpen Ω) (κ χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (hχS : tsupport χ.function ⊆ S) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (z : ℂ) (hz : z ≠ 0) (d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      H.val.2 j x = -(Complex.I * z) * (FlatDifferenceCoercivity.dielectric d x : ℂ) * E.val.1 j x) :
    ∃ D : L2Scalar, HasWeakDivergence
      (fun j => mulWeight d hd
        (scaleL2 χ.function χ.regular.continuous χ.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 j))) D := by
  let c : ℂ := -(Complex.I * z)
  have hc : c ≠ 0 := neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero hz)
  let P : L2Vector := extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2)
  let W : L2Vector := fun j => mulWeight d hd
    (scaleL2 χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j))
  let D : L2Scalar := extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest H.val.2)
  have hdiv : DomainCurl.DivergenceFree Ω H.val.2 := by
    intro f hf hfcomp hfin
    exact DomainCurl.weak_divergence_curl Ω H.property f hf hfcomp hfin
  have hpdiv : HasWeakDivergence P D := smooth_divergence_to_weak P D
    (divergence_cutoff_extend hΩ χ hχ hdiv)
  have hpw : ∀ j, P j = c • W j := by
    intro j
    apply Lp.ext
    have hp := extendScalar_ae Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2 j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp
      (mulL2_ae Ω χ.function χ.regular.continuous χ.compact (H.val.2 j))
    have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ E j)
    have hmax := (ae_restrict_iff' hΩ.measurableSet).mp hM
    filter_upwards [hp, hm, he, hmax, mulWeight_ae d hd
      (scaleL2 χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)),
      scaleL2_ae χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j),
      Lp.coeFn_smul c (W j)] with x hp hm he hmax hw hs hsm
    change extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.2 j) x = _
    rw [hp, hsm]
    change Ω.indicator (multiply Ω χ.toTest H.val.2 j) x = c * W j x
    change W j x = weight d x * _ at hw
    rw [hw, hs]
    by_cases hx : x ∈ tsupport χ.function
    · have hxS := hχS hx
      have hxΩ := hSΩ hxS
      have hκx : κ.function x = 1 := (hκ x hxS).self_of_nhds
      rw [Set.indicator_of_mem hxΩ]
      change mulL2 Ω χ.function χ.regular.continuous χ.compact (H.val.2 j) x = _
      rw [hm hxΩ, he hxΩ, hκx]
      simp only [one_mul]
      rw [hmax hxΩ j]
      simp only [weight, c]
      ring
    · have hz : χ.function x = 0 := image_eq_zero_of_nmem_tsupport hx
      by_cases hxΩ : x ∈ Ω
      · rw [Set.indicator_of_mem hxΩ]
        change mulL2 Ω χ.function χ.regular.continuous χ.compact (H.val.2 j) x = _
        rw [hm hxΩ, hz]
        simp
      · simp [hxΩ, hz]
  refine ⟨c⁻¹ • D, ?_⟩
  intro φ
  have h := hpdiv φ
  simp only [hpw, map_smul, smul_eq_mul] at h ⊢
  have hi : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  have hh := congrArg (fun z : ℂ => c⁻¹ * z) h
  simp only [mul_zero] at hh
  calc
    _ = c⁻¹ * (valuePair φ D + c * derivativePair φ 0 (W 0) +
        c * derivativePair φ 1 (W 1) + c * derivativePair φ 2 (W 2)) := by
      rw [mul_add, mul_add, mul_add]
      simp only [← mul_assoc, hi, one_mul]
      rfl
    _ = 0 := hh

end OQ14.Packet05WeightedDivergence
#print axioms OQ14.Packet05WeightedDivergence.actual_cutoff_weighted_divergence
#print axioms OQ14.Packet05WeightedDivergence.complex_cutoff_weighted_divergence
#print axioms OQ14.Packet05WeightedDivergence.cutoff_divergence_vanishes_on

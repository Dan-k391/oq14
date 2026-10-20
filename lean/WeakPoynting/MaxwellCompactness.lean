import WeakPoynting.ElectricControl

/-! # Full local L2 compactness of weak Maxwell fields with positive permittivity -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaxwellCompactness

open MeasureTheory OQ14.Maxwell OQ14.CurlCutoff OQ14.WeakConservation
  OQ14.WeakEnergy OQ14.ElectricControl OQ14.WeakCompactness
  OQ14.MagneticCompactness OQ14.LocalRegularity Filter
open scoped Topology Manifold

theorem multiply_sub {Ω : Set Space} (χ : DomainCurl.Test Ω)
    (u v : DomainCurl.L2Vector Ω) : multiply Ω χ.toTest (u - v) =
      multiply Ω χ.toTest u - multiply Ω χ.toTest v := by
  funext j
  apply Lp.ext
  filter_upwards [
    mulL2_ae Ω χ.function χ.regular.continuous χ.compact (u j - v j),
    mulL2_ae Ω χ.function χ.regular.continuous χ.compact (u j),
    mulL2_ae Ω χ.function χ.regular.continuous χ.compact (v j),
    Lp.coeFn_sub (u j) (v j),
    Lp.coeFn_sub (multiply Ω χ.toTest u j) (multiply Ω χ.toTest v j)]
    with x hd hu hv hs ht
  change mulL2 Ω χ.function χ.regular.continuous χ.compact (u j - v j) x =
    (multiply Ω χ.toTest u j - multiply Ω χ.toTest v j) x
  rw [hd, ht]
  change _ = mulL2 Ω χ.function χ.regular.continuous χ.compact (u j) x -
    mulL2 Ω χ.function χ.regular.continuous χ.compact (v j) x
  rw [hu, hv, hs]
  simp only [Pi.sub_apply, mul_sub]

theorem extendScalar_sub {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (u v : DomainCurl.L2Scalar Ω) :
    extendScalar Ω hΩ (u - v) = extendScalar Ω hΩ u - extendScalar Ω hΩ v := by
  apply Lp.ext
  have hsub := (ae_restrict_iff' hΩ).mp (Lp.coeFn_sub u v)
  filter_upwards [extendScalar_ae Ω hΩ (u - v), extendScalar_ae Ω hΩ u,
    extendScalar_ae Ω hΩ v, Lp.coeFn_sub (extendScalar Ω hΩ u) (extendScalar Ω hΩ v),
    hsub] with x hd hu hv he hs
  rw [hd, he]
  simp only [Pi.sub_apply]
  rw [hu, hv]
  by_cases hx : x ∈ Ω
  · simpa only [Set.indicator_of_mem hx, Pi.sub_apply] using hs hx
  · simp [Set.indicator_of_not_mem hx]

theorem cutField_sub {Ω : Set Space} (hΩ : IsOpen Ω) (χ : DomainCurl.Test Ω)
    (u v : DomainCurl.L2Vector Ω) :
    cutField hΩ χ (u - v) = cutField hΩ χ u - cutField hΩ χ v := by
  unfold cutField
  rw [multiply_sub]
  funext j
  exact extendScalar_sub hΩ.measurableSet _ _

theorem maxwell_sub {Ω : Set Space} (ω : ℝ) (μ ε : Space → ℝ)
    (E₁ H₁ E₂ H₂ : DomainCurl.HCurl Ω)
    (h₁ : WeakMaxwell ω μ ε E₁ H₁) (h₂ : WeakMaxwell ω μ ε E₂ H₂) :
    WeakMaxwell ω μ ε (E₁ - E₂) (H₁ - H₂) := by
  have h := CrossFlux.maxwell_combine ω μ ε (E₁, H₁) (E₂, H₂) h₁ h₂ (-1)
  change WeakMaxwell ω μ ε (E₁ + (-1 : ℂ) • E₂) (H₁ + (-1 : ℂ) • H₂) at h
  rw [neg_one_smul ℂ E₂, neg_one_smul ℂ H₂] at h
  simpa only [sub_eq_add_neg] using h

theorem exists_real_cutoff {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ζ : RealTest Ω, ContDiff ℝ 2 ζ.function ∧
      (∀ x, ‖ζ.function x‖ ≤ 1) ∧
      ∀ x ∈ K, ζ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  obtain ⟨V, hV, hKV, hVΩ, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨f, hf1, hf0, hf01⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, Space)) (t := V) hK.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support (f : Space → ℝ) ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (hf0 x hn)
  have hts : tsupport (f : Space → ℝ) ⊆ closure V := closure_mono hs
  have hreg : ContDiff ℝ 2 (f : Space → ℝ) :=
    f.contMDiff.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨⟨f, hreg.of_le (by norm_num),
    hcV.of_isClosed_subset isClosed_closure hts, hts.trans hVΩ⟩, hreg, ?_, ?_⟩
  · intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf01 x).1] using (hf01 x).2
  · intro x hx
    exact hf1.filter_mono (nhds_le_nhdsSet hx)

theorem exists_gradient_bound {Ω : Set Space} (ζ : RealTest Ω) :
    ∃ d : ℝ, ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2 := by
  obtain ⟨_, B, _, hB, _, hd⟩ := cutoff_bounds ζ.complexTest.toTest
  refine ⟨3 * B, ?_⟩
  intro x
  have hb (j : Fin 3) : |gradient ζ x j| ≤ B := by
    have hh := hd j x
    rw [realTest_partial] at hh
    simpa only [Complex.norm_real, Real.norm_eq_abs, WeakEnergy.gradient] using hh
  have hs (j : Fin 3) : (gradient ζ x j)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb j)
  dsimp [realEnergy]
  nlinarith [hs 0, hs 1, hs 2, sq_nonneg B]

/-- The electric cutoff family is controlled by an actual precompact magnetic
cutoff family. The control applies to differences of genuine Maxwell solutions. -/
theorem maxwell_electric_cutoff_precompact {ι : Type*} {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (hζ : ∀ x, ‖ζ.function x‖ ≤ 1)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {m M L : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hεlo : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x)
    (hεhi : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ι → DomainCurl.HCurl Ω)
    (hMax : ∀ t, WeakMaxwell ω (fun _ => 1) ε (E t) (H t))
    (hE : ∀ t, ‖(E t).val.1‖ ≤ L) (hH : ∀ t, ‖(H t).val.1‖ ≤ L) :
    IsCompact (closure (Set.range (fun t => cutField hΩ ζ.complexTest (E t).val.1))) := by
  obtain ⟨χ, hχ, hχS⟩ := exists_c2_interior_cutoff hΩ ζ.compact ζ.inside
  have hχone : ∀ x ∈ tsupport ζ.function, χ.function x = 1 :=
    fun x hx => (hχS x hx).self_of_nhds
  obtain ⟨d, hd⟩ := exists_gradient_bound ζ
  have hmag := maxwell_cutoff_precompact hΩ χ hχ ω hω ε hM hL hεhi E H hMax hE hH
  apply isCompact_of_totallyBounded_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply totallyBounded_range_of_controlled _
    (fun t => cutField hΩ χ (H t).val.1)
    (C := Real.sqrt (3 * (2 + 4 * d ^ 2 / (ω ^ 2 * m)) / m))
    (Real.sqrt_nonneg _)
    (hmag.totallyBounded.subset subset_closure)
  intro s t
  have hc := electric_cutoff_norm_control hΩ ζ χ hχone hζ d hd ω hω ε
    (E s - E t) (H s - H t)
    (maxwell_sub ω (fun _ => 1) ε (E s) (H s) (E t) (H t) (hMax s) (hMax t))
    m hm hεlo
  change ‖cutField hΩ ζ.complexTest ((E s).val.1 - (E t).val.1)‖ ≤
    _ * ‖cutField hΩ χ ((H s).val.1 - (H t).val.1)‖ at hc
  simpa only [cutField_sub, dist_eq_norm] using hc

theorem maxwell_cutoff_pair_precompact {ι : Type*} {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (hζ2 : ContDiff ℝ 2 ζ.function)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {m M L : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hεlo : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x)
    (hεhi : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ι → DomainCurl.HCurl Ω)
    (hMax : ∀ t, WeakMaxwell ω (fun _ => 1) ε (E t) (H t))
    (hE : ∀ t, ‖(E t).val.1‖ ≤ L) (hH : ∀ t, ‖(H t).val.1‖ ≤ L) :
    IsCompact (closure (Set.range (fun t =>
      (cutField hΩ ζ.complexTest (E t).val.1, cutField hΩ ζ.complexTest (H t).val.1)))) := by
  have he := maxwell_electric_cutoff_precompact hΩ ζ hζ ω hω ε hm hM hL hεlo hεhi
    E H hMax hE hH
  have hh := maxwell_cutoff_precompact hΩ ζ.complexTest
    (Complex.ofRealCLM.contDiff.comp hζ2) ω hω ε hM hL hεhi E H hMax hE hH
  have hp := he.prod hh
  apply hp.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro _ ⟨t, rfl⟩
    exact ⟨subset_closure (Set.mem_range_self t), subset_closure (Set.mem_range_self t)⟩
  · exact hp.isClosed

theorem cutField_agrees_on {Ω U : Set Space} (hΩ : IsOpen Ω) (hU : MeasurableSet U)
    (hUΩ : U ⊆ Ω) (χ : DomainCurl.Test Ω) (hχ : ∀ x ∈ U, χ.function x = 1)
    (u : DomainCurl.HCurl Ω) (j : Fin 3) :
    (fun x => cutField hΩ χ u.val.1 j x) =ᵐ[volume.restrict U] (fun x => u.val.1 j x) := by
  have hh := (ae_restrict_iff' hΩ.measurableSet).mp
    (LocalPower.cutExtend_field_ae hΩ χ u j)
  apply (ae_restrict_iff' hU).mpr
  filter_upwards [hh] with x hx
  intro hxu
  change (LocalPower.cutExtend hΩ χ u).val.1 j x = u.val.1 j x
  rw [hx (hUΩ hxu), hχ x hxu, one_mul]

/-- Full interior L2 compactness of the electric and magnetic fields follows
from actual weak Maxwell equations and uniform positive bounded permittivity.
The same cutoff and neighborhood work for the entire family. -/
theorem maxwell_local_precompact {ι : Type*} {Ω K : Set Space}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {m M L : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hεlo : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x)
    (hεhi : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ι → DomainCurl.HCurl Ω)
    (hMax : ∀ t, WeakMaxwell ω (fun _ => 1) ε (E t) (H t))
    (hE : ∀ t, ‖(E t).val.1‖ ≤ L) (hH : ∀ t, ‖(H t).val.1‖ ≤ L) :
    ∃ (U : Set Space) (F : ι → WeakCurl.L2Vector × WeakCurl.L2Vector),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧ IsCompact (closure (Set.range F)) ∧
      ∀ t j,
        ((fun x => (F t).1 j x) =ᵐ[volume.restrict U] (fun x => (E t).val.1 j x)) ∧
        ((fun x => (F t).2 j x) =ᵐ[volume.restrict U] (fun x => (H t).val.1 j x)) := by
  obtain ⟨ζ, hζ2, hζ, hζK⟩ := exists_real_cutoff hΩ hK hKΩ
  let U := interior {x | ζ.function x = 1} ∩ Ω
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have hUΩ : U ⊆ Ω := Set.inter_subset_right
  have hKU : K ⊆ U := by
    intro x hx
    exact ⟨mem_interior_iff_mem_nhds.mpr (hζK x hx), hKΩ hx⟩
  have hunit : ∀ x ∈ U, ζ.complexTest.function x = 1 := by
    intro x hx
    have he : ζ.function x = 1 :=
      (show interior {y | ζ.function y = 1} ⊆ {y | ζ.function y = 1}
        from interior_subset) hx.1
    simp [RealTest.complexTest, he]
  refine ⟨U, fun t => (cutField hΩ ζ.complexTest (E t).val.1,
    cutField hΩ ζ.complexTest (H t).val.1), hU, hKU, hUΩ,
    maxwell_cutoff_pair_precompact hΩ ζ hζ2 hζ ω hω ε hm hM hL hεlo hεhi E H hMax hE hH, ?_⟩
  intro t j
  exact ⟨cutField_agrees_on hΩ hU.measurableSet hUΩ ζ.complexTest hunit (E t) j,
    cutField_agrees_on hΩ hU.measurableSet hUΩ ζ.complexTest hunit (H t) j⟩

theorem maxwell_local_subsequence {Ω K : Set Space}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {m M L : ℝ}
    (hm : 0 < m) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hεlo : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x)
    (hεhi : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ℕ → DomainCurl.HCurl Ω)
    (hMax : ∀ n, WeakMaxwell ω (fun _ => 1) ε (E n) (H n))
    (hE : ∀ n, ‖(E n).val.1‖ ≤ L) (hH : ∀ n, ‖(H n).val.1‖ ≤ L) :
    ∃ (U : Set Space) (F : ℕ → WeakCurl.L2Vector × WeakCurl.L2Vector)
      (G : WeakCurl.L2Vector × WeakCurl.L2Vector) (s : ℕ → ℕ),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      (∀ n j,
        ((fun x => (F n).1 j x) =ᵐ[volume.restrict U] (fun x => (E n).val.1 j x)) ∧
        ((fun x => (F n).2 j x) =ᵐ[volume.restrict U] (fun x => (H n).val.1 j x))) ∧
      StrictMono s ∧ Tendsto (F ∘ s) atTop (𝓝 G) := by
  obtain ⟨U, F, hU, hKU, hUΩ, hc, he⟩ :=
    maxwell_local_precompact hΩ hK hKΩ ω hω ε hm hM hL hεlo hεhi E H hMax hE hH
  obtain ⟨G, _, s, hs, ht⟩ :=
    hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨U, F, G, s, hU, hKU, hUΩ, he, hs, ht⟩

end OQ14.MaxwellCompactness

#print axioms OQ14.MaxwellCompactness.multiply_sub
#print axioms OQ14.MaxwellCompactness.extendScalar_sub
#print axioms OQ14.MaxwellCompactness.cutField_sub
#print axioms OQ14.MaxwellCompactness.maxwell_sub
#print axioms OQ14.MaxwellCompactness.exists_real_cutoff
#print axioms OQ14.MaxwellCompactness.exists_gradient_bound
#print axioms OQ14.MaxwellCompactness.maxwell_electric_cutoff_precompact
#print axioms OQ14.MaxwellCompactness.maxwell_cutoff_pair_precompact
#print axioms OQ14.MaxwellCompactness.cutField_agrees_on
#print axioms OQ14.MaxwellCompactness.maxwell_local_precompact
#print axioms OQ14.MaxwellCompactness.maxwell_local_subsequence

import LocalizedCurlCurlSource
import MaxwellCurlCutoffSource
import FlatDifferenceCoercivity

/-! Actual local flat-interface Maxwell fields and their cutoff source bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.FlatLocalCurlSources
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCurlCutoffSource OQ14.CurlCutoff

theorem extend_weighted {Ω : Set Space} (hΩ : IsOpen Ω) (d : ℝ)
    (W C : DomainCurl.L2Vector Ω)
    (hWC : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      W j x = MaxwellWeakTranslation.flatWeight d x * C j x) :
    ∀ j, (fun x => extendVector Ω hΩ.measurableSet W j x) =ᵐ[volume]
      fun x => MaxwellWeakTranslation.flatWeight d x * extendVector Ω hΩ.measurableSet C j x := by
  intro j
  have he := (ae_restrict_iff' hΩ.measurableSet).mp hWC
  filter_upwards [extendScalar_ae Ω hΩ.measurableSet (W j),
    extendScalar_ae Ω hΩ.measurableSet (C j), he] with x hW hC hx
  change extendScalar Ω hΩ.measurableSet (W j) x =
    MaxwellWeakTranslation.flatWeight d x * extendScalar Ω hΩ.measurableSet (C j) x
  rw [hW,hC]
  by_cases h : x ∈ Ω
  · simpa [Set.indicator_of_mem h] using hx h j
  · simp [Set.indicator_of_not_mem h]

theorem actual_flat_local_sources {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (k d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) (FlatDifferenceCoercivity.dielectric d) E H)
    (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ l x, ‖dcoord χ.function x l‖ ≤ A)
    (hB : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ B) :
    ∃ (W : DomainCurl.HCurl Ω) (u : WeakCurl.HCurl) (Wext Cext : L2Vector),
      (∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
        W.val.1 j x = (((FlatDifferenceCoercivity.dielectric d x)⁻¹ : ℝ) : ℂ) * H.val.2 j x) ∧
      (∀ j, (fun x => Wext j x) =ᵐ[volume] fun x => MaxwellWeakTranslation.flatWeight d x * Cext j x) ∧
      (∀ j, (fun x => u.val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => χ.function x * (k^2 : ℂ) * H.val.1 j x +
          dcoord χ.function x (next j) * W.val.1 (previous j) x -
          dcoord χ.function x (previous j) * W.val.1 (next j) x) ∧
      ∀ i j, i ≠ 2 → ∀ h : ℝ, h ≠ 0 →
        ‖quotient (source χ.toTest hχ Wext j) i h‖ ≤
          A * (‖quotient (Cext (previous j)) i h‖ + ‖quotient (Cext (next j)) i h‖) +
            3*B*(‖Wext (previous j)‖ + ‖Wext (next j)‖) := by
  have hε : ∀ x, 0 < FlatDifferenceCoercivity.dielectric d x :=
    fun x => lt_of_lt_of_le zero_lt_one (FlatDifferenceCoercivity.dielectric_bounds d hd x).1
  obtain ⟨W,u,hW,hsource,_⟩ := LocalizedCurlCurlSource.cutoff_curlcurl_source hΩ χ k _ hε E H hM
  let Wext := extendVector Ω hΩ.measurableSet W.val.1
  let Cext := extendVector Ω hΩ.measurableSet H.val.2
  have hweight : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      W.val.1 j x = MaxwellWeakTranslation.flatWeight d x * H.val.2 j x := by
    filter_upwards [hW] with x hx j
    rw [FlatDifferenceCoercivity.flatWeight_eq_inverse]
    exact hx j
  have hglobal := extend_weighted hΩ d W.val.1 H.val.2 hweight
  refine ⟨W,u,Wext,Cext,hW,hglobal,hsource,?_⟩
  intro i j hi h hh
  exact flat_quotient_source_bound χ.toTest hχ Wext Cext d hd i j hi h hh A B hA0 hA hB hglobal

end OQ14.FlatLocalCurlSources
#print axioms OQ14.FlatLocalCurlSources.actual_flat_local_sources

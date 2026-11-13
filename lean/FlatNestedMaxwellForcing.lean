import FlatLocalCurlSources
import NestedCurlCutoffSource

/-! Nested forcing for actual regional Maxwell fields at a flat dielectric jump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.FlatNestedMaxwellForcing
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.CurlCutoff
  OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCurlCutoffSource OQ14.NestedCurlCutoffSource

theorem actual_nested_forcing {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function) (η : Test)
    (hη : ∀ x ∈ tsupport χ.function, η.function x = 1)
    (k d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) (FlatDifferenceCoercivity.dielectric d) E H)
    (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ l x, ‖dcoord χ.function x l‖ ≤ A)
    (hB : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ B) :
    ∃ (W : DomainCurl.HCurl Ω) (u : WeakCurl.HCurl) (Wext Cext : L2Vector),
      (∀ j, (fun x => Wext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => W.val.1 j x) ∧
      (∀ j, (fun x => Cext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => H.val.2 j x) ∧
      (∀ j, (fun x => u.val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => χ.function x * (k^2 : ℂ) * H.val.1 j x + source χ.toTest hχ Wext j x) ∧
      ∀ i j, i ≠ 2 → ∀ h : ℝ, h ≠ 0 →
        ‖quotient (source χ.toTest hχ Wext j) i h‖ ≤
          A * (‖quotient (localize η Cext (previous j)) i h‖ +
            ‖quotient (localize η Cext (next j)) i h‖) +
          3*B*(‖localize η Wext (previous j)‖ + ‖localize η Wext (next j)‖) := by
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
  have hglobal := FlatLocalCurlSources.extend_weighted hΩ d W.val.1 H.val.2 hweight
  have hWext (j : Fin 3) : (fun x => Wext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => W.val.1 j x :=
    LocalPower.extendScalar_ae_region hΩ.measurableSet (W.val.1 j)
  have hCext (j : Fin 3) : (fun x => Cext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => H.val.2 j x :=
    LocalPower.extendScalar_ae_region hΩ.measurableSet (H.val.2 j)
  refine ⟨W,u,Wext,Cext,hWext,hCext,?_,?_⟩
  · intro j
    filter_upwards [hsource j, ae_restrict_of_ae (source_ae χ.toTest hχ Wext j),
      hWext (previous j), hWext (next j)] with x hu hs hp hn
    rw [hu,hs,hp,hn]
    ring
  · intro i j hi h hh
    exact nested_flat_source_bound χ.toTest η hχ hη Wext Cext d hd i j hi h hh A B hA0 hA hB hglobal

end OQ14.FlatNestedMaxwellForcing
#print axioms OQ14.FlatNestedMaxwellForcing.actual_nested_forcing

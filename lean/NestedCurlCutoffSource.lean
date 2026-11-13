import MaxwellCurlCutoffSource
import RegionalMaxwellHelmholtz

/-! Nested cutoffs remove artificial region-boundary terms from curl sources. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.NestedCurlCutoffSource
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCurlCutoffSource

def localize (η : Test) (W : L2Vector) : L2Vector :=
  fun j => scaleL2 η.function η.regular.continuous η.compact (W j)

theorem source_localize (χ η : Test) (hχ : ContDiff ℝ 2 χ.function)
    (hη : ∀ x ∈ tsupport χ.function, η.function x = 1)
    (W : L2Vector) (j : Fin 3) :
    source χ hχ (localize η W) j = source χ hχ W j := by
  apply Lp.ext
  filter_upwards [source_ae χ hχ (localize η W) j, source_ae χ hχ W j,
    scaleL2_ae η.function η.regular.continuous η.compact (W (previous j)),
    scaleL2_ae η.function η.regular.continuous η.compact (W (next j))] with x hs ht hp hn
  rw [hs, ht]
  change localize η W (previous j) x = _ at hp
  change localize η W (next j) x = _ at hn
  rw [hp,hn]
  by_cases hx : x ∈ tsupport χ.function
  · rw [hη x hx]
    simp
  · have hzero (l : Fin 3) : dcoord χ.function x l = 0 := by
      simp [dcoord, fderiv_of_not_mem_tsupport ℝ hx]
    simp [hzero]

theorem localize_weighted (η : Test) (W C : L2Vector) (w : Space → ℂ)
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume] fun x => w x * C j x) :
    ∀ j, (fun x => localize η W j x) =ᵐ[volume] fun x => w x * localize η C j x := by
  intro j
  filter_upwards [scaleL2_ae η.function η.regular.continuous η.compact (W j),
    scaleL2_ae η.function η.regular.continuous η.compact (C j), hWC j] with x hw hc he
  change localize η W j x = _ at hw
  change localize η C j x = _ at hc
  rw [hw,hc,he]
  ring

theorem nested_flat_source_bound (χ η : Test) (hχ : ContDiff ℝ 2 χ.function)
    (hη : ∀ x ∈ tsupport χ.function, η.function x = 1)
    (W C : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hi : i ≠ 2)
    (h : ℝ) (hh : h ≠ 0) (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ l x, ‖dcoord χ.function x l‖ ≤ A)
    (hB : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ B)
    (hWC : ∀ l, (fun x => W l x) =ᵐ[volume] fun x => MaxwellWeakTranslation.flatWeight d x * C l x) :
    ‖quotient (source χ hχ W j) i h‖ ≤
      A * (‖quotient (localize η C (previous j)) i h‖ + ‖quotient (localize η C (next j)) i h‖) +
        3*B*(‖localize η W (previous j)‖ + ‖localize η W (next j)‖) := by
  rw [← source_localize χ η hχ hη W j]
  exact flat_quotient_source_bound χ hχ (localize η W) (localize η C) d hd i j hi h hh A B hA0 hA hB
    (localize_weighted η W C _ hWC)

end OQ14.NestedCurlCutoffSource
#print axioms OQ14.NestedCurlCutoffSource.nested_flat_source_bound

import Packet05TransverseDivCurl
import GlobalToRegionalCurl
import WeakPoynting.LocalRegularity

/-! Local H¹ regularity of the actual transverse projection, with no
frequency restriction and no material derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05TransverseLocalH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.DivCurlRegularity OQ14.LocalRegularity
  OQ14.CurlCutoff OQ14.GlobalToRegionalCurl OQ14.Packet05TransverseDivergence
  OQ14.Packet05LongitudinalCurl OQ14.Packet05TransverseDivCurl

theorem transverse_cutoff_h1 (F : VectorFourier.VectorL2) (C : L2Vector)
    (hF : HasWeakCurl (coordinateVector F) C) (χ : Test)
    (hχ : ContDiff ℝ 2 χ.function) :
    ∃ W : L2Vector, ∃ G : DerivativeIndex → L2Scalar,
      (∀ j, (fun x => W j x) =ᵐ[volume]
        fun x => χ.function x * coordinateVector (transverse F) j x) ∧
      (∀ p, HasWeakPartial (W p.2) (G p) p.1) := by
  obtain ⟨hdiv,hcurl,_⟩ := transverse_divcurl F C hF
  let V : HCurl := ⟨(coordinateVector (transverse F), C), hcurl⟩
  obtain ⟨E,hE,hC⟩ := restrict_global_hcurl isOpen_univ V
  have hD : DomainCurl.DivergenceFree Set.univ E.val.1 := by
    intro f hf hc hi
    let φ : Test := ⟨f, hf.of_le (by norm_num), hc⟩
    have hh := hdiv φ
    simp only [valuePair, derivativePair, testPair_integral, map_zero, zero_add] at hh
    have he (i : Fin 3) : (∫ x in Set.univ, E.val.1 i x * dcoord f x i) =
        ∫ x, coordinateVector (transverse F) i x * dcoord f x i := by
      simp only [DomainCurl.regionMeasure, Measure.restrict_univ, Measure.restrict_restrict,
        Set.univ_inter]
      apply integral_congr_ae
      have hEi : (fun x => E.val.1 i x) =ᵐ[volume] fun x => coordinateVector (transverse F) i x := by
        simpa only [DomainCurl.regionMeasure, Measure.restrict_univ] using hE i
      filter_upwards [hEi] with x hx
      change E.val.1 i x = coordinateVector (transverse F) i x at hx
      rw [hx]
    rw [he 0, he 1, he 2]
    simpa only [φ] using hh
  let ψ : DomainCurl.Test Set.univ := ⟨χ, Set.subset_univ _⟩
  obtain ⟨G,hG,_⟩ := cutoff_divcurl_regularity isOpen_univ ψ hχ E hD
  let W := extendVector Set.univ isOpen_univ.measurableSet (multiply Set.univ ψ.toTest E.val.1)
  refine ⟨W,G,?_,hG⟩
  intro j
  have hext := extendScalar_ae Set.univ isOpen_univ.measurableSet (multiply Set.univ ψ.toTest E.val.1 j)
  have hm := mulL2_ae Set.univ χ.function χ.regular.continuous χ.compact (E.val.1 j)
  have hmU : (fun x => mulL2 Set.univ χ.function χ.regular.continuous χ.compact (E.val.1 j) x) =ᵐ[volume]
      fun x => χ.function x * E.val.1 j x := by
    simpa only [DomainCurl.regionMeasure, Measure.restrict_univ] using hm
  have heU : (fun x => E.val.1 j x) =ᵐ[volume] fun x => coordinateVector (transverse F) j x := by
    simpa only [DomainCurl.regionMeasure, Measure.restrict_univ] using hE j
  filter_upwards [hext, hmU, heU] with x hx hm he
  change extendScalar Set.univ isOpen_univ.measurableSet (multiply Set.univ ψ.toTest E.val.1 j) x = _
  rw [hx]
  simp only [Set.indicator_univ]
  change mulL2 Set.univ χ.function χ.regular.continuous χ.compact (E.val.1 j) x = _
  rw [hm,he]

end OQ14.Packet05TransverseLocalH1
#print axioms OQ14.Packet05TransverseLocalH1.transverse_cutoff_h1

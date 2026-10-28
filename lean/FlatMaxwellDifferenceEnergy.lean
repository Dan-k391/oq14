import MaxwellWeakTranslation
import WeakPoynting.Poynting

/-! Actual weak Green identity for flat-interface magnetic finite differences. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.FlatMaxwellDifferenceEnergy
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.WeakPower

theorem flat_difference_green (H C W : L2Vector) (d k : ℝ)
    (hH : HasWeakCurl H C) (hW : HasWeakCurl W ((k^2 : ℂ) • H))
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume] fun x => flatWeight d x * C j x)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (ζ : Test) :
    localGreenIntegral ζ (quotientVector W i h) (quotientVector ((k^2 : ℂ) • H) i h)
      (conjVector (quotientVector H i h)) (conjVector (quotientVector C i h)) = 0 ∧
    (∀ j, (fun x => quotientVector W i h j x) =ᵐ[volume]
      fun x => flatWeight d x * quotientVector C i h j x) := by
  have hqH := quotient_weakCurl H C hH i h
  have hqW := flat_curlcurl_quotient H C W d k hW hWC i hi h
  let u : HCurl := ⟨(quotientVector W i h, quotientVector ((k^2 : ℂ) • H) i h), hqW.1⟩
  let v : HCurl := ⟨(quotientVector H i h, quotientVector C i h), hqH⟩
  have he := weak_local_Green ζ u (conjHCurl v)
  refine ⟨?_,hqW.2⟩
  exact he

end OQ14.FlatMaxwellDifferenceEnergy
#print axioms OQ14.FlatMaxwellDifferenceEnergy.flat_difference_green

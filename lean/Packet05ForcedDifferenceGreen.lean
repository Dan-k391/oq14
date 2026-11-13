import MaxwellWeakTranslation
import WeakPoynting.Poynting
import MaxwellCurlCutoffSource

/-! Green identity for the inhomogeneous inverse-curl equation.  The forcing
is retained explicitly; the homogeneous case alone cannot handle cutoffs. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ForcedDifferenceGreen
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.WeakPower
  OQ14.MaxwellCutoffCommutator

/-- A tangential quotient sees the material law whenever both endpoints lie
in the region where that law holds.  This permits global cutoff extensions
without claiming the original equation at the artificial boundary. -/
theorem localized_weight_quotient (W C : L2Vector) (w : Space → ℂ)
    (S : Set Space) (i : Fin 3) (h : ℝ)
    (hweight : ∀ x, w (x + h • basis i) = w x)
    (hWC : ∀ j, ∀ᵐ x ∂volume, x ∈ S → W j x = w x * C j x) :
    ∀ j, ∀ᵐ x ∂volume, x ∈ S → x + h • basis i ∈ S →
      quotientVector W i h j x = w x * quotientVector C i h j x := by
  intro j
  have ht := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae (hWC j)
  filter_upwards [hWC j, ht, quotient_ae (W j) i h, quotient_ae (C j) i h] with x hw ht hwq hcq hx hxt
  change MaxwellDifferenceQuotient.quotient (W j) i h x =
    w x * MaxwellDifferenceQuotient.quotient (C j) i h x
  rw [hwq, hcq, hw hx, ht hxt, hweight]
  ring

theorem forced_flat_difference_green (H C W F : L2Vector) (d : ℝ)
    (hH : HasWeakCurl H C) (hW : HasWeakCurl W F)
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume] fun x => flatWeight d x * C j x)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (ζ : Test) :
    localGreenIntegral ζ (quotientVector W i h) (quotientVector F i h)
      (conjVector (quotientVector H i h)) (conjVector (quotientVector C i h)) = 0 ∧
    (∀ j, (fun x => quotientVector W i h j x) =ᵐ[volume]
      fun x => flatWeight d x * quotientVector C i h j x) := by
  let u : HCurl := ⟨(quotientVector W i h, quotientVector F i h),
    quotient_weakCurl W F hW i h⟩
  let v : HCurl := ⟨(quotientVector H i h, quotientVector C i h),
    quotient_weakCurl H C hH i h⟩
  refine ⟨weak_local_Green ζ u (conjHCurl v), ?_⟩
  exact quotient_commutes_invariant_weight W C (flatWeight d) i h
    (flatWeight_tangential d i hi h) hWC

/-- The cutoff commutator R is kept in the tangential difference identity. -/
theorem forced_flat_difference_green_with_commutator
    (H C W F R : L2Vector) (d : ℝ)
    (hH : HasWeakCurl H C) (hW : HasWeakCurl W F)
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume]
      fun x => flatWeight d x * C j x + R j x)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (ζ : Test) :
    localGreenIntegral ζ (quotientVector W i h) (quotientVector F i h)
      (conjVector (quotientVector H i h)) (conjVector (quotientVector C i h)) = 0 ∧
    (∀ j, (fun x => quotientVector W i h j x) =ᵐ[volume]
      fun x => flatWeight d x * quotientVector C i h j x + quotientVector R i h j x) := by
  let V : L2Vector := W - R
  have hV : ∀ j, (fun x => V j x) =ᵐ[volume] fun x => flatWeight d x * C j x := by
    intro j
    filter_upwards [hWC j, Lp.coeFn_sub (W j) (R j)] with x hw hs
    change ((W j - R j : L2Scalar) : Space → ℂ) x = _ at hs
    change ((W j - R j : L2Scalar) : Space → ℂ) x = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hw]
    simp
  have hq := quotient_commutes_invariant_weight V C (flatWeight d) i h
    (flatWeight_tangential d i hi h) hV
  let u : HCurl := ⟨(quotientVector W i h, quotientVector F i h),
    quotient_weakCurl W F hW i h⟩
  let v : HCurl := ⟨(quotientVector H i h, quotientVector C i h),
    quotient_weakCurl H C hH i h⟩
  refine ⟨weak_local_Green ζ u (conjHCurl v), ?_⟩
  intro j
  have hv := hq j
  change (fun x => MaxwellDifferenceQuotient.quotient (W j - R j) i h x) =ᵐ[volume] _ at hv
  rw [MaxwellCurlCutoffSource.quotient_sub] at hv
  filter_upwards [hv, Lp.coeFn_sub (quotientVector W i h j) (quotientVector R i h j)] with x hx hs
  change ((quotientVector W i h j - quotientVector R i h j : L2Scalar) : Space → ℂ) x = _ at hx hs
  rw [hs] at hx
  simp only [Pi.sub_apply] at hx
  exact sub_eq_iff_eq_add.mp hx

end OQ14.Packet05ForcedDifferenceGreen
#print axioms OQ14.Packet05ForcedDifferenceGreen.forced_flat_difference_green
#print axioms OQ14.Packet05ForcedDifferenceGreen.forced_flat_difference_green_with_commutator
#print axioms OQ14.Packet05ForcedDifferenceGreen.localized_weight_quotient

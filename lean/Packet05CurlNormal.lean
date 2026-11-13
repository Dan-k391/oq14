import Packet05DifferenceMaxwell

/-! Recover normal tangential-component derivatives from curl and tangential
derivatives, with all equations interpreted distributionally. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CurlNormal
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.WeakPoynting OQ14.WeakGreen OQ14.Packet05DifferenceMaxwell

theorem normal_first_from_curl (E C : L2Vector) (hC : HasWeakCurl E C)
    (D : L2Scalar) (hD : HasWeakPartial (E 2) D 0) :
    HasWeakPartial (E 0) (C 1 + D) 2 := by
  intro φ
  have hc := hC φ 1
  have hd := hD φ
  change (derivativePair φ 0 (E 2) - derivativePair φ 2 (E 0)) - valuePair φ (C 1) = 0 at hc
  simp only [map_add]
  linear_combination -hc + hd

theorem normal_second_from_curl (E C : L2Vector) (hC : HasWeakCurl E C)
    (D : L2Scalar) (hD : HasWeakPartial (E 2) D 1) :
    HasWeakPartial (E 1) (D - C 0) 2 := by
  intro φ
  have hc := hC φ 0
  have hd := hD φ
  change (derivativePair φ 2 (E 1) - derivativePair φ 1 (E 2)) - valuePair φ (C 0) = 0 at hc
  simp only [map_sub]
  linear_combination hc + hd

/-- Any compact C1 localization of an H(curl) field has a global weak curl. -/
theorem cutoff_has_weakCurl (u : HCurl) (χ : Test) :
    ∃ C : L2Vector, HasWeakCurl
      (fun j => scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 j)) C := by
  obtain ⟨U, hU, _⟩ := GlobalToRegionalCurl.restrict_global_hcurl isOpen_univ u
  let χu : DomainCurl.Test Set.univ := ⟨χ, Set.subset_univ _⟩
  let v := LocalPower.cutExtend isOpen_univ χu U
  have hf : v.val.1 = fun j => scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 j) := by
    funext j
    exact cutField_global_ae isOpen_univ χu (U.val.1 j) (u.val.1 j) (hU j)
  refine ⟨v.val.2, ?_⟩
  rw [← hf]
  exact v.property

theorem cutoff_normal_tangential_components (u : HCurl) (χ : Test)
    (D0 D1 : L2Scalar)
    (h0 : HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 2)) D0 0)
    (h1 : HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 2)) D1 1) :
    (∃ v, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 0)) v 2) ∧
    (∃ v, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (u.val.1 1)) v 2) := by
  obtain ⟨C, hc⟩ := cutoff_has_weakCurl u χ
  exact ⟨⟨C 1 + D0, normal_first_from_curl _ C hc D0 h0⟩,
    ⟨D1 - C 0, normal_second_from_curl _ C hc D1 h1⟩⟩

end OQ14.Packet05CurlNormal
#print axioms OQ14.Packet05CurlNormal.normal_first_from_curl
#print axioms OQ14.Packet05CurlNormal.normal_second_from_curl
#print axioms OQ14.Packet05CurlNormal.cutoff_has_weakCurl
#print axioms OQ14.Packet05CurlNormal.cutoff_normal_tangential_components

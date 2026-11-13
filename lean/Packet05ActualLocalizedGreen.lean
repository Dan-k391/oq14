import Packet05ForcedDifferenceGreen
import MaxwellInverseCurlCurl
import FlatDifferenceCoercivity

/-! Actual flat Maxwell fields localized for tangential Green testing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualLocalizedGreen
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.WeakPower
  OQ14.Packet05ForcedDifferenceGreen
open scoped Topology

/-- Genuine regional Maxwell fields produce global H(curl) test fields whose
inverse-weight relation holds on every interior set on which the cutoff is
locally one.  It is not asserted at the artificial cutoff boundary. -/
theorem actual_localized_flat_fields {Ω S : Set Space} (hΩ : IsOpen Ω)
    (κ : DomainCurl.Test Ω) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H) :
    ∃ u v : WeakCurl.HCurl,
      (∀ j, ∀ᵐ x ∂volume, x ∈ S →
        u.val.1 j x = MaxwellWeakTranslation.flatWeight d x * v.val.2 j x) ∧
      (∀ j, ∀ᵐ x ∂volume, x ∈ S →
        u.val.2 j x = (k^2 : ℂ) * v.val.1 j x) := by
  have hε : ∀ x, 0 < FlatDifferenceCoercivity.dielectric d x :=
    fun x => lt_of_lt_of_le zero_lt_one (FlatDifferenceCoercivity.dielectric_bounds d hd x).1
  obtain ⟨W, hW, hWae⟩ := MaxwellInverseCurlCurl.inverse_curl_representation k _ hε E H hM
  let w : DomainCurl.HCurl Ω := ⟨(W, (k^2 : ℂ) • H.val.1), hW⟩
  let u := LocalPower.cutExtend hΩ κ w
  let v := LocalPower.cutExtend hΩ κ H
  refine ⟨u, v, ?_, ?_⟩
  · intro j
    have hu := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ w j)
    have hv := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ κ H j)
    have hw := (ae_restrict_iff' hΩ.measurableSet).mp hWae
    filter_upwards [hu, hv, hw] with x hu hv hw hx
    have hκx : κ.function x = 1 := (hκ x hx).self_of_nhds
    have hdκ : ∀ l, dcoord κ.function x l = 0 := by
      intro l
      simp [dcoord, (hκ x hx).fderiv_eq]
    rw [hu (hSΩ hx), hv (hSΩ hx), hκx, hdκ, hdκ]
    simp only [one_mul, zero_mul, add_zero, sub_zero]
    rw [FlatDifferenceCoercivity.flatWeight_eq_inverse]
    exact hw (hSΩ hx) j
  · intro j
    have hu := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ κ w j)
    have hv := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ H j)
    have hs := (ae_restrict_iff' hΩ.measurableSet).mp
      (Lp.coeFn_smul (k^2 : ℂ) (H.val.1 j))
    filter_upwards [hu, hv, hs] with x hu hv hs hx
    have hκx : κ.function x = 1 := (hκ x hx).self_of_nhds
    have hdκ : ∀ l, dcoord κ.function x l = 0 := by
      intro l
      simp [dcoord, (hκ x hx).fderiv_eq]
    rw [hu (hSΩ hx), hv (hSΩ hx), hκx, hdκ, hdκ]
    simp only [one_mul, zero_mul, add_zero, sub_zero]
    exact hs (hSΩ hx)

/-- The actual Maxwell equations yield the translated Green identity and the
coercive weight and mass identities on the common interior of both endpoints. -/
theorem actual_flat_tangential_green {Ω S : Set Space} (hΩ : IsOpen Ω)
    (κ : DomainCurl.Test Ω) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H) :
    ∃ u v : WeakCurl.HCurl,
      ∀ (i : Fin 3), i ≠ 2 → ∀ (h : ℝ) (ζ : WeakCurl.Test),
        localGreenIntegral ζ (quotientVector u.val.1 i h) (quotientVector u.val.2 i h)
          (conjVector (quotientVector v.val.1 i h))
          (conjVector (quotientVector v.val.2 i h)) = 0 ∧
        (∀ j, ∀ᵐ x ∂volume, x ∈ S → x + h • basis i ∈ S →
          quotientVector u.val.1 i h j x = flatWeight d x * quotientVector v.val.2 i h j x) ∧
        (∀ j, ∀ᵐ x ∂volume, x ∈ S → x + h • basis i ∈ S →
          quotientVector u.val.2 i h j x = (k^2 : ℂ) * quotientVector v.val.1 i h j x) := by
  obtain ⟨u, v, hu, hv⟩ := actual_localized_flat_fields hΩ κ hSΩ hκ k d hd E H hM
  refine ⟨u, v, ?_⟩
  intro i hi h ζ
  let uq : HCurl := ⟨(quotientVector u.val.1 i h, quotientVector u.val.2 i h),
    quotient_weakCurl u.val.1 u.val.2 u.property i h⟩
  let vq : HCurl := ⟨(quotientVector v.val.1 i h, quotientVector v.val.2 i h),
    quotient_weakCurl v.val.1 v.val.2 v.property i h⟩
  refine ⟨weak_local_Green ζ uq (conjHCurl vq), ?_, ?_⟩
  · exact localized_weight_quotient u.val.1 v.val.2 (flatWeight d) S i h
      (flatWeight_tangential d i hi h) hu
  · exact localized_weight_quotient u.val.2 v.val.1 (fun _ => (k^2 : ℂ)) S i h
      (fun _ => rfl) hv

end OQ14.Packet05ActualLocalizedGreen
#print axioms OQ14.Packet05ActualLocalizedGreen.actual_localized_flat_fields
#print axioms OQ14.Packet05ActualLocalizedGreen.actual_flat_tangential_green

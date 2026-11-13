import MaxwellWeakTranslation
import MaxwellInverseCurlCurl

/-! The actual cutoff forcing in the magnetic inverse-weight curl–curl equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.LocalizedCurlCurlSource
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.MaxwellWeakTranslation

theorem cutoff_curlcurl_source {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (k : ℝ) (ε : Space → ℝ) (hε : ∀ x, 0 < ε x)
    (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    ∃ (W : DomainCurl.HCurl Ω) (u : WeakCurl.HCurl),
      (∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
        W.val.1 j x = (((ε x)⁻¹ : ℝ) : ℂ) * H.val.2 j x) ∧
      (∀ j, (fun x => u.val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => χ.function x * (k^2 : ℂ) * H.val.1 j x +
          dcoord χ.function x (WeakCurl.next j) * W.val.1 (WeakCurl.previous j) x -
          dcoord χ.function x (WeakCurl.previous j) * W.val.1 (WeakCurl.next j) x) ∧
      ∀ i h, HasWeakCurl (quotientVector u.val.1 i h) (quotientVector u.val.2 i h) := by
  obtain ⟨W,hW,hWae⟩ := MaxwellInverseCurlCurl.inverse_curl_representation k ε hε E H hM
  let w : DomainCurl.HCurl Ω := ⟨(W, (k^2 : ℂ) • H.val.1),hW⟩
  let u : WeakCurl.HCurl := LocalPower.cutExtend hΩ χ w
  refine ⟨w,u,hWae,?_,?_⟩
  · intro j
    filter_upwards [LocalPower.cutExtend_curl_ae hΩ χ w j,
      Lp.coeFn_smul (k^2 : ℂ) (H.val.1 j)] with x hx hs
    change u.val.2 j x = _ at hx ⊢
    rw [hx]
    dsimp only [w, Pi.smul_apply]
    rw [hs]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro i h
    exact quotient_weakCurl u.val.1 u.val.2 u.property i h

end OQ14.LocalizedCurlCurlSource
#print axioms OQ14.LocalizedCurlCurlSource.cutoff_curlcurl_source

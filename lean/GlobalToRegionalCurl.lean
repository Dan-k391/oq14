import MaxwellWeakTranslation
import WeakPoynting.RegionalCurlUpgrade

/-! Restriction of an actual global weak curl to an open subregion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.GlobalToRegionalCurl
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl

theorem restrict_global_hcurl {Ω : Set Space} (hΩ : IsOpen Ω) (v : WeakCurl.HCurl) :
    ∃ u : DomainCurl.HCurl Ω,
      (∀ j, (fun x => u.val.1 j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => v.val.1 j x) ∧
      (∀ j, (fun x => u.val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => v.val.2 j x) := by
  let E : Field := fun x j => v.val.1 j x
  let C : Field := fun x j => v.val.2 j x
  have hE : ∀ j, MemLp (fun x => E x j) 2 (DomainCurl.regionMeasure Ω) :=
    fun j => (Lp.memLp (v.val.1 j)).mono_measure Measure.restrict_le_self
  have hC : ∀ j, MemLp (fun x => C x j) 2 (DomainCurl.regionMeasure Ω) :=
    fun j => (Lp.memLp (v.val.2 j)).mono_measure Measure.restrict_le_self
  have hc : DomainCurl.HasWeakCurl Ω (DomainCurl.fieldToL2 Ω E hE) (DomainCurl.fieldToL2 Ω C hC) := by
    apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ E C hE hC
    intro f hf hfc _ j
    let φ : WeakCurl.Test := ⟨f, hf.of_le (by norm_num), hfc⟩
    exact (WeakCurl.hasWeakCurl_iff_integral _ _).mp v.property φ j
  refine ⟨⟨(DomainCurl.fieldToL2 Ω E hE,DomainCurl.fieldToL2 Ω C hC),hc⟩,?_,?_⟩
  · intro j
    exact (hE j).coeFn_toLp
  · intro j
    exact (hC j).coeFn_toLp

theorem restrict_weakMaxwell {Ω : Set Space} (hΩ : IsOpen Ω) (k : ℝ) (ε : Space → ℝ)
    (e h : WeakCurl.HCurl)
    (he : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j,
      e.val.2 j x = Complex.I * (k : ℂ) * h.val.1 j x)
    (hh : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j,
      h.val.2 j x = -(Complex.I * (k : ℂ)) * (ε x : ℂ) * e.val.1 j x) :
    ∃ E H : DomainCurl.HCurl Ω,
      (∀ j, (fun x => E.val.1 j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => e.val.1 j x) ∧
      (∀ j, (fun x => H.val.1 j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => h.val.1 j x) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) ε E H := by
  obtain ⟨E,hE,hCE⟩ := restrict_global_hcurl hΩ e
  obtain ⟨H,hH,hCH⟩ := restrict_global_hcurl hΩ h
  refine ⟨E,H,hE,hH,?_,?_⟩
  · filter_upwards [he, ae_all_iff.mpr hCE, ae_all_iff.mpr hH] with x hx hcx hhx j
    rw [hcx j, hhx j, hx j]
    simp
  · filter_upwards [hh, ae_all_iff.mpr hCH, ae_all_iff.mpr hE] with x hx hcx hex j
    rw [hcx j, hex j]
    simpa only [neg_mul] using hx j

end OQ14.GlobalToRegionalCurl
#print axioms OQ14.GlobalToRegionalCurl.restrict_global_hcurl
#print axioms OQ14.GlobalToRegionalCurl.restrict_weakMaxwell

import WeakPoynting.Poynting
import HCurlCutoff
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Local weak complex Poynting law on arbitrary open regions

Only restricted-measure L2 fields and curls are required. A proved smooth
interior cutoff is identically one near the compact test support; its zero
extension allows the already proved whole-space weak law to apply.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.LocalPower

open MeasureTheory OQ14.Maxwell OQ14.CurlCutoff
open scoped ComplexConjugate Topology Manifold

def density (χ : WeakCurl.Test) (E C H K : Field) (x : Space) : ℂ :=
  χ.function x * (dot (C x) (conjugate (H x)) - dot (E x) (conjugate (K x))) +
  dot (fun j => dcoord χ.function x j) (crossProduct (E x) (conjugate (H x)))

theorem density_zero_off_support (χ : WeakCurl.Test) (E C H K : Field)
    {x : Space} (hx : x ∉ tsupport χ.function) : density χ E C H K x = 0 := by
  have hχ := image_eq_zero_of_nmem_tsupport hx
  have hd : ∀ j, dcoord χ.function x j = 0 := by
    intro j
    simp [dcoord, fderiv_of_not_mem_tsupport ℝ hx]
  simp [density, hχ, hd, dot]

theorem exists_interior_cutoff {Ω : Set Space} (hΩ : IsOpen Ω) (χ : DomainCurl.Test Ω) :
    ∃ κ : DomainCurl.Test Ω, ∀ x ∈ tsupport χ.function,
      κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  obtain ⟨V, hV, hKV, hVΩ, hcV⟩ :=
    exists_open_between_and_isCompact_closure χ.compact hΩ χ.inside
  obtain ⟨f, hf1, hf0, _⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, Space)) (t := V) χ.compact.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support (fun x => (f x : ℂ)) ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (by simp [hf0 x hn])
  have hts : tsupport (fun x => (f x : ℂ)) ⊆ closure V := closure_mono hs
  have hreg : ContDiff ℝ 1 (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (f.contMDiff.contDiff.of_le (by simp))
  refine ⟨⟨⟨_, hreg, hcV.of_isClosed_subset isClosed_closure hts⟩,
    hts.trans hVΩ⟩, ?_⟩
  intro x hx
  have he := hf1.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [he] with y hy
  simp only [hy, Complex.ofReal_one]

def cutExtend {Ω : Set Space} (hΩ : IsOpen Ω) (κ : DomainCurl.Test Ω)
    (u : DomainCurl.HCurl Ω) : WeakCurl.HCurl :=
  ⟨(extendVector Ω hΩ.measurableSet (multiply Ω κ.toTest u.val.1),
    extendVector Ω hΩ.measurableSet (productCurl Ω κ.toTest u.val.1 u.val.2)),
    weakCurl_cutoff_extend Ω hΩ κ u.property⟩

theorem extendScalar_ae_region {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (u : DomainCurl.L2Scalar Ω) :
    (fun x => extendScalar Ω hΩ u x) =ᵐ[DomainCurl.regionMeasure Ω] (fun x => u x) := by
  filter_upwards [ae_restrict_of_ae (extendScalar_ae Ω hΩ u), ae_restrict_mem hΩ] with x hx hm
  simpa [hm] using hx

theorem cutExtend_field_ae {Ω : Set Space} (hΩ : IsOpen Ω) (κ : DomainCurl.Test Ω)
    (u : DomainCurl.HCurl Ω) (j : Fin 3) :
    (fun x => (cutExtend hΩ κ u).val.1 j x) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => κ.function x * u.val.1 j x) := by
  exact (extendScalar_ae_region hΩ.measurableSet _).trans
    (mulL2_ae Ω κ.function κ.regular.continuous κ.compact _)

theorem productCurl_ae {Ω : Set Space} (κ : WeakCurl.Test)
    (E C : DomainCurl.L2Vector Ω) (j : Fin 3) :
    (fun x => productCurl Ω κ E C j x) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => κ.function x * C j x +
        dcoord κ.function x (WeakCurl.next j) * E (WeakCurl.previous j) x -
        dcoord κ.function x (WeakCurl.previous j) * E (WeakCurl.next j) x) := by
  filter_upwards [Lp.coeFn_sub
      (multiply Ω κ C j + derivativeMultiply Ω κ (WeakCurl.next j) (E (WeakCurl.previous j)))
      (derivativeMultiply Ω κ (WeakCurl.previous j) (E (WeakCurl.next j))),
    Lp.coeFn_add (multiply Ω κ C j) (derivativeMultiply Ω κ (WeakCurl.next j) (E (WeakCurl.previous j))),
    mulL2_ae Ω κ.function κ.regular.continuous κ.compact (C j),
    mulL2_ae Ω (fun x => dcoord κ.function x (WeakCurl.next j))
      (partial_continuous κ.regular _) (κ.compact.fderiv_apply ℝ (basis _)) (E (WeakCurl.previous j)),
    mulL2_ae Ω (fun x => dcoord κ.function x (WeakCurl.previous j))
      (partial_continuous κ.regular _) (κ.compact.fderiv_apply ℝ (basis _)) (E (WeakCurl.next j))]
    with x hs ha hv hd₁ hd₂
  change (multiply Ω κ C j + derivativeMultiply Ω κ (WeakCurl.next j) (E (WeakCurl.previous j)) -
      derivativeMultiply Ω κ (WeakCurl.previous j) (E (WeakCurl.next j))) x = _
  dsimp only [Pi.add_apply, Pi.sub_apply] at hs ha
  rw [hs, ha]
  dsimp only [multiply, derivativeMultiply]
  rw [hv, hd₁, hd₂]

theorem cutExtend_curl_ae {Ω : Set Space} (hΩ : IsOpen Ω) (κ : DomainCurl.Test Ω)
    (u : DomainCurl.HCurl Ω) (j : Fin 3) :
    (fun x => (cutExtend hΩ κ u).val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => κ.function x * u.val.2 j x +
        dcoord κ.function x (WeakCurl.next j) * u.val.1 (WeakCurl.previous j) x -
        dcoord κ.function x (WeakCurl.previous j) * u.val.1 (WeakCurl.next j) x) :=
  (extendScalar_ae_region hΩ.measurableSet _).trans (productCurl_ae κ.toTest _ _ j)

theorem cutExtend_density_ae {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ κ : DomainCurl.Test Ω)
    (hκ : ∀ x ∈ tsupport χ.function, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (E H : DomainCurl.HCurl Ω) :
    (fun x => WeakPower.poyntingDensity χ.toTest
      (cutExtend hΩ κ E).val.1 (cutExtend hΩ κ E).val.2
      (cutExtend hΩ κ H).val.1 (cutExtend hΩ κ H).val.2 x) =ᵐ[DomainCurl.regionMeasure Ω]
    (fun x => density χ.toTest (fun y j => E.val.1 j y) (fun y j => E.val.2 j y)
      (fun y j => H.val.1 j y) (fun y j => H.val.2 j y) x) := by
  have he := ae_all_iff.mpr (fun j => cutExtend_field_ae hΩ κ E j)
  have hc := ae_all_iff.mpr (fun j => cutExtend_curl_ae hΩ κ E j)
  have hh := ae_all_iff.mpr (fun j => cutExtend_field_ae hΩ κ H j)
  have hk := ae_all_iff.mpr (fun j => cutExtend_curl_ae hΩ κ H j)
  filter_upwards [he, hc, hh, hk] with x he hc hh hk
  by_cases hx : x ∈ tsupport χ.function
  · have hv : κ.function x = 1 := (hκ x hx).eq_of_nhds
    have hd : ∀ j, dcoord κ.function x j = 0 := by
      intro j
      simp [dcoord, (hκ x hx).fderiv_eq]
    simp only [hv, hd, one_mul, zero_mul, add_zero, sub_zero] at he hc hh hk
    simp only [WeakPower.poyntingDensity, density, he, hc, hh, hk]
  · have hv := image_eq_zero_of_nmem_tsupport hx
    have hd : ∀ j, dcoord χ.function x j = 0 := by
      intro j
      simp [dcoord, fderiv_of_not_mem_tsupport ℝ hx]
    simp [WeakPower.poyntingDensity, density, hv, hd, dot]

/-- Complex Poynting for arbitrary weak H(curl) fields on any open region.
Only regional L2 membership is imposed; no boundary condition is present. -/
theorem local_weak_complex_Poynting {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (E H : DomainCurl.HCurl Ω) :
    (∫ x in Ω, density χ.toTest (fun y j => E.val.1 j y) (fun y j => E.val.2 j y)
      (fun y j => H.val.1 j y) (fun y j => H.val.2 j y) x) = 0 := by
  obtain ⟨κ, hκ⟩ := exists_interior_cutoff hΩ χ
  have heq := integral_congr_ae (cutExtend_density_ae hΩ χ κ hκ E H)
  rw [← heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact WeakPower.weak_complex_Poynting χ.toTest (cutExtend hΩ κ E) (cutExtend hΩ κ H)
  · intro x hx
    have hn : x ∉ tsupport χ.function := fun hs => hx (χ.inside hs)
    have hv := image_eq_zero_of_nmem_tsupport hn
    have hd : ∀ j, dcoord χ.function x j = 0 := by
      intro j
      simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
    simp [WeakPower.poyntingDensity, hv, hd, dot]

theorem local_poyntingDensity_integrable {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (E H : DomainCurl.HCurl Ω) :
    Integrable (density χ.toTest (fun y j => E.val.1 j y) (fun y j => E.val.2 j y)
      (fun y j => H.val.1 j y) (fun y j => H.val.2 j y)) (DomainCurl.regionMeasure Ω) := by
  obtain ⟨κ, hκ⟩ := exists_interior_cutoff hΩ χ
  exact (WeakPower.poyntingDensity_integrable χ.toTest (cutExtend hΩ κ E).val.1
    (cutExtend hΩ κ E).val.2 (cutExtend hΩ κ H).val.1 (cutExtend hΩ κ H).val.2).restrict.congr
      (cutExtend_density_ae hΩ χ κ hκ E H)

end OQ14.LocalPower

#print axioms OQ14.LocalPower.exists_interior_cutoff
#print axioms OQ14.LocalPower.cutExtend_field_ae
#print axioms OQ14.LocalPower.cutExtend_curl_ae
#print axioms OQ14.LocalPower.cutExtend_density_ae
#print axioms OQ14.LocalPower.local_weak_complex_Poynting
#print axioms OQ14.LocalPower.local_poyntingDensity_integrable

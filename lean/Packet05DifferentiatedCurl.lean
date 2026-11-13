import Packet05PartialProduct
import WeakPoynting.RegionalCurlUpgrade
import Packet05FlatWeight

/-! Local differentiation of an actual weak curl equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DifferentiatedCurl
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05CurlCommutation

/-- If curl F equals a times H on U, then the actual weak tangential
derivatives satisfy curl (∂ᵢF)=a ∂ᵢH on U.  The equality of the original
curl is needed only locally, not across the artificial cutoff boundary. -/
theorem differentiated_local_curl_pairing (U : Set Space) (F C H DF DH : L2Vector)
    (a : ℂ) (i : Fin 3) (hcurl : HasWeakCurl F C)
    (hF : ∀ j, HasWeakPartial (F j) (DF j) i)
    (hH : ∀ j, HasWeakPartial (H j) (DH j) i)
    (hCH : ∀ j, ∀ᵐ x ∂volume, x ∈ U → C j x = a * H j x)
    (φ : Test) (hφ : ContDiff ℝ 2 φ.function) (hφU : tsupport φ.function ⊆ U)
    (j : Fin 3) : weakCurl φ j DF = a * valuePair φ (DH j) := by
  let ψ := partialTest φ hφ i
  let α := partialTest φ hφ (previous j)
  let β := partialTest φ hφ (next j)
  have hpair : valuePair ψ (C j) = a * valuePair ψ (H j) := by
    simp only [valuePair, testPair_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hCH j] with x hx
    by_cases hxu : x ∈ U
    · rw [hx hxu]
      ring
    · have hnot : x ∉ tsupport φ.function := fun hx => hxu (hφU hx)
      have hz : ψ.function x = 0 := by
        simp [ψ, partialTest, dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
      simp [hz]
  have hc := hcurl ψ j
  have h1 := hF (next j) α
  have h2 := hF (previous j) β
  have h3 := hH j φ
  have ha := derivativePair_partial_comm φ hφ i (previous j) (F (next j))
  have hb := derivativePair_partial_comm φ hφ i (next j) (F (previous j))
  change derivativePair ψ (previous j) (F (next j)) -
    derivativePair ψ (next j) (F (previous j)) - valuePair ψ (C j) = 0 at hc
  change valuePair α (DF (next j)) + derivativePair α i (F (next j)) = 0 at h1
  change valuePair β (DF (previous j)) + derivativePair β i (F (previous j)) = 0 at h2
  change valuePair φ (DH j) + valuePair ψ (H j) = 0 at h3
  change derivativePair ψ (previous j) (F (next j)) = derivativePair α i (F (next j)) at ha
  change derivativePair ψ (next j) (F (previous j)) = derivativePair β i (F (previous j)) at hb
  have hα : valuePair α (DF (next j)) = derivativePair φ (previous j) (DF (next j)) := rfl
  have hβ : valuePair β (DF (previous j)) = derivativePair φ (next j) (DF (previous j)) := rfl
  rw [ha, hb, hpair] at hc
  rw [hα] at h1
  rw [hβ] at h2
  change derivativePair φ (previous j) (DF (next j)) -
    derivativePair φ (next j) (DF (previous j)) = a * valuePair φ (DH j)
  linear_combination -hc + h1 - h2 - a*h3

/-- Differentiate both genuine local Maxwell curl equations.  The electric
displacement derivative is kept explicit, so the coefficient may jump. -/
theorem differentiated_local_maxwell_pairing (U : Set Space)
    (E CE H CH W DE DH DW : L2Vector) (z : ℂ) (i : Fin 3)
    (hE : HasWeakCurl E CE) (hH : HasWeakCurl H CH)
    (hDE : ∀ j, HasWeakPartial (E j) (DE j) i)
    (hDH : ∀ j, HasWeakPartial (H j) (DH j) i)
    (hDW : ∀ j, HasWeakPartial (W j) (DW j) i)
    (hCE : ∀ j, ∀ᵐ x ∂volume, x ∈ U → CE j x = (Complex.I*z) * H j x)
    (hCH : ∀ j, ∀ᵐ x ∂volume, x ∈ U → CH j x = -(Complex.I*z) * W j x)
    (φ : Test) (hφ : ContDiff ℝ 2 φ.function) (hφU : tsupport φ.function ⊆ U)
    (j : Fin 3) :
    weakCurl φ j DE = (Complex.I*z) * valuePair φ (DH j) ∧
    weakCurl φ j DH = -(Complex.I*z) * valuePair φ (DW j) := by
  exact ⟨differentiated_local_curl_pairing U E CE H DE DH (Complex.I*z) i hE hDE hDH hCE φ hφ hφU j,
    differentiated_local_curl_pairing U H CH W DH DW (-(Complex.I*z)) i hH hDH hDW hCH φ hφ hφU j⟩

/-- Smooth differentiated curl tests and the actual displacement relation
produce genuine regional H(curl) Maxwell fields. -/
theorem regional_maxwell_of_differentiated_pairings {U : Set Space} (hU : IsOpen U)
    (DE DH DW : L2Vector) (k d : ℝ) (hd : 0 ≤ d)
    (hW : ∀ j, DW j = Packet05FlatWeight.mulWeight d hd (DE j))
    (hpair : ∀ (φ : Test), ContDiff ℝ 2 φ.function → tsupport φ.function ⊆ U → ∀ j,
      weakCurl φ j DE = (Complex.I*(k : ℂ)) * valuePair φ (DH j) ∧
      weakCurl φ j DH = -(Complex.I*(k : ℂ)) * valuePair φ (DW j)) :
    ∃ E H : DomainCurl.HCurl U,
      (∀ j, (fun x => E.val.1 j x) =ᵐ[DomainCurl.regionMeasure U] fun x => DE j x) ∧
      (∀ j, (fun x => H.val.1 j x) =ᵐ[DomainCurl.regionMeasure U] fun x => DH j x) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) (FlatDifferenceCoercivity.dielectric d) E H := by
  let e : Field := fun x j => DE j x
  let h : Field := fun x j => DH j x
  let ce : Field := fun x j => (Complex.I*(k : ℂ)) * DH j x
  let ch : Field := fun x j => -(Complex.I*(k : ℂ)) * DW j x
  have he : ∀ j, MemLp (fun x => e x j) 2 (DomainCurl.regionMeasure U) :=
    fun j => (Lp.memLp (DE j)).mono_measure Measure.restrict_le_self
  have hh : ∀ j, MemLp (fun x => h x j) 2 (DomainCurl.regionMeasure U) :=
    fun j => (Lp.memLp (DH j)).mono_measure Measure.restrict_le_self
  have hce : ∀ j, MemLp (fun x => ce x j) 2 (DomainCurl.regionMeasure U) :=
    fun j => ((Lp.memLp (DH j)).const_mul (Complex.I*(k : ℂ))).mono_measure Measure.restrict_le_self
  have hch : ∀ j, MemLp (fun x => ch x j) 2 (DomainCurl.regionMeasure U) :=
    fun j => ((Lp.memLp (DW j)).const_mul (-(Complex.I*(k : ℂ)))).mono_measure Measure.restrict_le_self
  have hcurlE := RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hU e ce he hce (by
    intro f hf hc hs j
    let φ : Test := ⟨f, hf.of_le (by norm_num), hc⟩
    have hp := (hpair φ (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hs j).1
    rw [weakCurl_integral, valuePair, testPair_integral, ← integral_const_mul] at hp
    simpa only [φ, e, ce, mul_assoc] using hp.symm)
  have hcurlH := RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hU h ch hh hch (by
    intro f hf hc hs j
    let φ : Test := ⟨f, hf.of_le (by norm_num), hc⟩
    have hp := (hpair φ (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hs j).2
    rw [weakCurl_integral, valuePair, testPair_integral, ← integral_const_mul] at hp
    simpa only [φ, h, ch, mul_assoc] using hp.symm)
  let E : DomainCurl.HCurl U := ⟨(DomainCurl.fieldToL2 U e he, DomainCurl.fieldToL2 U ce hce), hcurlE⟩
  let H : DomainCurl.HCurl U := ⟨(DomainCurl.fieldToL2 U h hh, DomainCurl.fieldToL2 U ch hch), hcurlH⟩
  refine ⟨E, H, (fun j => (he j).coeFn_toLp), (fun j => (hh j).coeFn_toLp), ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun j => (hce j).coeFn_toLp),
      ae_all_iff.mpr (fun j => (hh j).coeFn_toLp)] with x hcex hhx j
    change (hce j).toLp (fun x => ce x j) x =
      Complex.I * (k : ℂ) * (1 : ℂ) * (hh j).toLp (fun x => h x j) x
    rw [hcex j, hhx j]
    simp [ce, h]
  · have hw (j : Fin 3) : (fun x => DW j x) =ᵐ[DomainCurl.regionMeasure U]
        fun x => (FlatDifferenceCoercivity.dielectric d x : ℂ) * DE j x := by
      rw [hW j]
      exact ae_restrict_of_ae (Packet05FlatWeight.mulWeight_ae d hd (DE j))
    filter_upwards [ae_all_iff.mpr (fun j => (hch j).coeFn_toLp),
      ae_all_iff.mpr (fun j => (he j).coeFn_toLp), ae_all_iff.mpr hw] with x hchx hex hwx j
    change (hch j).toLp (fun x => ch x j) x =
      -Complex.I * (k : ℂ) * (FlatDifferenceCoercivity.dielectric d x : ℂ) *
        (he j).toLp (fun x => e x j) x
    rw [hchx j, hex j]
    simp only [ch, e]
    rw [hwx j]
    ring

end OQ14.Packet05DifferentiatedCurl
#print axioms OQ14.Packet05DifferentiatedCurl.differentiated_local_curl_pairing
#print axioms OQ14.Packet05DifferentiatedCurl.differentiated_local_maxwell_pairing
#print axioms OQ14.Packet05DifferentiatedCurl.regional_maxwell_of_differentiated_pairings

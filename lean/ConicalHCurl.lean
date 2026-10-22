import ConicalComplexTests
import WeakPoynting.RegionalCurlUpgrade

/-! The genuine conical electric field belongs to regional H(curl), with zero curl. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalHCurl
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ConicalCapField OQ14.ConicalComplexTests
open scoped Topology ENNReal

theorem electric_memLp_bounded (ν a t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hb : Bornology.IsBounded Ω) (i : Fin 3) :
    MemLp (fun x => complexElectric ν a t x i) 2 (DomainCurl.regionMeasure Ω) := by
  obtain ⟨R,hR⟩ := hb.subset_closedBall (0 : Space)
  have hi : MemLp (fun x => electric ν a t x i) 2 (volume.restrict (closedBall 0 R)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).comp_memLp'
      (electric_memLp_two_ball ν a t R hν ha ht ht1)
  exact hi.ofReal.mono_measure (Measure.restrict_mono hR le_rfl)

def localElectricL2 (ν a t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hb : Bornology.IsBounded Ω) : DomainCurl.L2Vector Ω :=
  DomainCurl.fieldToL2 Ω (complexElectric ν a t) (electric_memLp_bounded ν a t hν ha ht ht1 Ω hb)

def zeroCurlL2 (Ω : Set Space) : DomainCurl.L2Vector Ω :=
  DomainCurl.fieldToL2 Ω (fun _ _ => 0) (fun _ => MemLp.zero')

theorem local_hasWeakCurl (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    DomainCurl.HasWeakCurl Ω (localElectricL2 ν a t hν.le ha ht ht1 Ω hb) (zeroCurlL2 Ω) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ
  intro ψ hψ hc _ j
  simp only [zero_mul,integral_zero]
  have h := ConicalComplexTests.weak_cross_pair ν a t hν ha ht ht1 ψ
    (hψ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hc (WeakCurl.next j) (WeakCurl.previous j)
  rw [h,sub_self]

def localElectric (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) : DomainCurl.HCurl Ω :=
  ⟨(localElectricL2 ν a t hν.le ha ht ht1 Ω hb,zeroCurlL2 Ω),local_hasWeakCurl ν a t hν ha ht ht1 Ω hΩ hb⟩

theorem localElectric_field_ae (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (i : Fin 3) :
    ((localElectric ν a t hν ha ht ht1 Ω hΩ hb).val.1 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
      fun x => complexElectric ν a t x i :=
  (electric_memLp_bounded ν a t hν.le ha ht ht1 Ω hb i).coeFn_toLp

theorem localElectric_curl_ae_zero (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (Ω : Set Space) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (i : Fin 3) :
    ((localElectric ν a t hν ha ht ht1 Ω hΩ hb).val.2 i : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω] 0 :=
  (MemLp.zero' (μ := DomainCurl.regionMeasure Ω) (ε := ℂ) (p := 2)).coeFn_toLp

end OQ14.ConicalHCurl

#print axioms OQ14.ConicalHCurl.electric_memLp_bounded
#print axioms OQ14.ConicalHCurl.local_hasWeakCurl
#print axioms OQ14.ConicalHCurl.localElectric_field_ae
#print axioms OQ14.ConicalHCurl.localElectric_curl_ae_zero

import Packet05TransmissionContinuity
import Packet05SecondTangential

/-! Actual one-sided continuous representatives for a flat dielectric jump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualContinuous
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05SecondTangential
  OQ14.Packet05FlatTransmissionH1 OQ14.Packet05TransmissionContinuity
open scoped Topology

theorem actual_flat_one_sided_continuous {Ω U : Set Space}
    (hΩ : IsOpen Ω) (c₀ : Space) (r₀ R₀ : ℝ) (hr₀ : r₀ < R₀)
    (κ₀ : DomainCurl.Test Ω) (hκ₀2 : ContDiff ℝ 2 κ₀.function)
    (hS₀ : Metric.ball c₀ R₀ ⊆ Ω)
    (hκ₀ : ∀ x ∈ Metric.ball c₀ R₀, κ₀.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A₀ B₀ : ℝ) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hvκ₀ : ∀ x, ‖κ₀.function x‖ ≤ A₀) (hdκ₀ : ∀ l x, ‖dcoord κ₀.function x l‖ ≤ B₀)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ₀ : WeakConservation.RealTest (Metric.ball c₀ r₀))
    (hζ₀2 : ContDiff ℝ 2 ζ₀.complexTest.function) (η₀ : DomainCurl.Test (Metric.ball c₀ r₀))
    (hη₀ : ∀ x ∈ tsupport ζ₀.function, η₀.function x = 1)
    (hζ₀ : ∀ x, ‖ζ₀.function x‖ ≤ 1) (L₀ C₀ D₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hgrad₀ : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ₀ x) ≤ L₀^2)
    (hηbound₀ : ∀ x, ‖η₀.function x‖ ≤ C₀)
    (hζder₀ : ∀ l x, ‖dcoord ζ₀.complexTest.function x l‖ ≤ D₀)
    (hUopen : IsOpen U) (hU : U ⊆ Metric.ball c₀ r₀)
    (hζunit₀ : ∀ x ∈ U, ζ₀.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (c₁ : Space) (r₁ R₁ : ℝ) (hr₁ : r₁ < R₁)
    (κ₁ : DomainCurl.Test U) (hκ₁2 : ContDiff ℝ 2 κ₁.function)
    (hS₁ : Metric.ball c₁ R₁ ⊆ U)
    (hκ₁ : ∀ x ∈ Metric.ball c₁ R₁, κ₁.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A₁ B₁ : ℝ) (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hvκ₁ : ∀ x, ‖κ₁.function x‖ ≤ A₁) (hdκ₁ : ∀ l x, ‖dcoord κ₁.function x l‖ ≤ B₁)
    (ζ₁ : WeakConservation.RealTest (Metric.ball c₁ r₁))
    (hζ₁2 : ContDiff ℝ 2 ζ₁.complexTest.function) (η₁ : DomainCurl.Test (Metric.ball c₁ r₁))
    (hη₁ : ∀ x ∈ tsupport ζ₁.function, η₁.function x = 1)
    (hζ₁ : ∀ x, ‖ζ₁.function x‖ ≤ 1) (L₁ C₁ D₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hgrad₁ : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ₁ x) ≤ L₁^2)
    (hηbound₁ : ∀ x, ‖η₁.function x‖ ≤ C₁)
    (hζder₁ : ∀ l x, ‖dcoord ζ₁.complexTest.function x l‖ ≤ D₁)
    (V : Set Space) (hVU : V ⊆ U)
    (hζ₁unit : ∀ x ∈ V, ζ₁.complexTest.function x = 1)
    (ε₀ : ℝ) (hε₀ : ε₀ ≠ 0)
    (hε : ∀ x ∈ V, FlatDifferenceCoercivity.dielectric d x = ε₀)
    (hVopen : IsOpen V) :
    ∃ reps : Fin 3 → Space → ℂ,
      (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E.val.1 j x) =ᵐ[volume.restrict V] reps j) := by
  let F : L2Vector := fun j => scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous
    ζ₀.complexTest.compact ((LocalPower.cutExtend hΩ κ₀ E).val.1 j)
  let T : L2Vector := fun j => transmissionComponent d hd F j
  obtain ⟨D,hD⟩ := actual_flat_transmission_h1 hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀
  have hsecond := actual_second_tangential_derivatives hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
  have hgraphs : ∀ i, i ≠ 2 → ∃ (DE : L2Vector) (G : Fin 3 → Fin 3 → L2Scalar),
      (∀ j, HasWeakPartial (F j) (DE j) i) ∧
      (∀ t j, HasWeakPartial (transmissionComponent d hd
        (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) j) (G t j) t) := by
    intro i hi
    obtain ⟨DE,hDE,_,G,hG⟩ := hsecond i hi
    exact ⟨DE,G,hDE,fun t j => (hG t j).1⟩
  have hcont := cutoff_transmission_continuous F d hd D hD ζ₁.complexTest.toTest hζ₁2 hgraphs
  classical
  choose R hRcont hRae using hcont
  let reps : Fin 3 → Space → ℂ := fun j x => if j = 2 then ((ε₀ : ℂ)⁻¹) * R j x else R j x
  refine ⟨reps, ?_, ?_⟩
  · intro j
    by_cases hj : j = 2
    · simpa [reps, hj] using (continuous_const.mul (hRcont j))
    · simpa [reps, hj] using hRcont j
  · have hball : Metric.ball c₀ r₀ ⊆ Metric.ball c₀ R₀ := Metric.ball_subset_ball hr₀.le
    let χ : DomainCurl.Test Ω := ⟨ζ₀.complexTest.toTest, ζ₀.complexTest.inside.trans (hball.trans hS₀)⟩
    have hχS : tsupport χ.function ⊆ Metric.ball c₀ R₀ := ζ₀.complexTest.inside.trans hball
    have hF : ∀ j, (fun x => F j x) =ᵐ[volume.restrict V] fun x => E.val.1 j x := by
      intro j
      have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ χ E j)
      have hn : (LocalPower.cutExtend hΩ χ E).val.1 j = F j :=
        Packet05ActualDifferentiatedMaxwell.nested_cutoff_field Ω (Metric.ball c₀ R₀) hΩ κ₀ χ hχS hS₀ hκ₀ E j
      apply (ae_restrict_iff' hVopen.measurableSet).mpr
      filter_upwards [he] with x hx hxV
      have hxU := hVU hxV
      have hxΩ := hS₀ (hball (hU hxU))
      have hχx : χ.function x = 1 := (hζunit₀ x hxU).self_of_nhds
      rw [← hn, hx hxΩ, hχx, one_mul]
    intro j
    have hRt : (fun x => T j x) =ᵐ[volume.restrict V] R j := by
      have hr : (fun x => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (T j) x) =ᵐ[volume.restrict V] R j := ae_restrict_of_ae (hRae j)
      filter_upwards [hr, ae_restrict_of_ae (scaleL2_ae ζ₁.complexTest.function
        ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (T j)),
        ae_restrict_mem hVopen.measurableSet] with x hr hs hxV
      change scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (T j) x = R j x at hr
      rw [hs, hζ₁unit x hxV, one_mul] at hr
      exact hr
    by_cases hj : j = 2
    · subst j
      have hw : (fun x => Packet05FlatWeight.mulWeight d hd (F 2) x) =ᵐ[volume.restrict V]
          fun x => Packet05FlatWeight.weight d x * F 2 x :=
        ae_restrict_of_ae (Packet05FlatWeight.mulWeight_ae d hd (F 2))
      filter_upwards [hRt, hF 2, hw, ae_restrict_mem hVopen.measurableSet] with x ht hf hw hxV
      change Packet05FlatWeight.mulWeight d hd (F 2) x = R 2 x at ht
      rw [hw, hf] at ht
      have hn : (ε₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε₀
      change E.val.1 2 x = ((ε₀ : ℂ)⁻¹) * R 2 x
      rw [← ht]
      simp only [Packet05FlatWeight.weight, hε x hxV]
      field_simp
    · filter_upwards [hRt, hF j] with x ht hf
      have ht' : F j x = R j x := by simpa [T, transmissionComponent, hj] using ht
      simpa [reps, hj] using hf.symm.trans ht'

end OQ14.Packet05ActualContinuous
#print axioms OQ14.Packet05ActualContinuous.actual_flat_one_sided_continuous

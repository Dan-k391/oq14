import Packet05ActualNormalNormal
import Packet05RegionalPartial

/-! Actual phasewise H2 in weak-derivative form for a flat interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualFlatH2
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05SecondTangential
  OQ14.Packet05ActualNormalNormal OQ14.Packet05RegionalPartial
open scoped Topology

theorem actual_flat_phase_h2 {Ω U : Set Space}
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
    ∃ (D : Fin 3 → Fin 3 → L2Scalar) (Hess : Fin 3 → Fin 3 → Fin 3 → L2Scalar),
      (∀ j, (fun x => scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 j) x) =ᵐ[volume.restrict V]
        fun x => E.val.1 j x) ∧
      (∀ i j, HasPartialOn V
        (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 j)) (D i j) i) ∧
      (∀ t i j, HasPartialOn V (D i j) (Hess t i j) t) := by
  have hsecond := actual_second_tangential_derivatives hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
  obtain ⟨DE0,hDE0,_,G0,hG0⟩ := hsecond 0 (by decide)
  obtain ⟨DE1,hDE1,_,G1,hG1⟩ := hsecond 1 (by decide)
  obtain ⟨N2,Q2,_,hN2,hQ2⟩ := actual_phase_normal_normal hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁ V hVU hζ₁unit ε₀ hε₀ hε
  obtain ⟨N0,Q0,N1,Q1,hN0,hQ0,hN1,hQ1⟩ := actual_phase_tangential_normal_normal
    hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀ A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM
    ζ₀ hζ₀2 η₀ hη₀ hζ₀ L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁ V hVU hζ₁unit ε₀ hε₀ hε
  let F : L2Vector := fun j => scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous
    ζ₀.complexTest.compact ((LocalPower.cutExtend hΩ κ₀ E).val.1 j)
  let Nv : L2Vector := ![N0,N1,((ε₀ : ℂ)⁻¹) • N2]
  let Qv : L2Vector := ![Q0,Q1,Q2]
  let deriv : Fin 3 → Fin 3 → L2Scalar := fun i j => ![DE0 j, DE1 j, Nv j] i
  have hfield : ∀ j, (fun x => F j x) =ᵐ[volume.restrict V] fun x => E.val.1 j x := by
    have hball : Metric.ball c₀ r₀ ⊆ Metric.ball c₀ R₀ := Metric.ball_subset_ball hr₀.le
    let χ : DomainCurl.Test Ω := ⟨ζ₀.complexTest.toTest, ζ₀.complexTest.inside.trans (hball.trans hS₀)⟩
    have hχS : tsupport χ.function ⊆ Metric.ball c₀ R₀ := ζ₀.complexTest.inside.trans hball
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
  have hfirst : ∀ i j, HasPartialOn V (F j) (deriv i j) i := by
    intro i j
    fin_cases i
    · exact global_partial_on V _ _ 0 (hDE0 j)
    · exact global_partial_on V _ _ 1 (hDE1 j)
    · fin_cases j
      · exact hN0
      · exact hN1
      · exact hN2
  have hnsecond : ∀ j, HasPartialOn V (Nv j) (Qv j) 2 := by
    intro j
    fin_cases j
    · exact hQ0
    · exact hQ1
    · exact hQ2
  have hcut : ∀ (v : L2Scalar), ∀ᵐ x ∂volume, x ∈ V →
      v x = scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact v x := by
    intro v
    filter_upwards [scaleL2_ae ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact v] with x hx hxV
    rw [hx, hζ₁unit x hxV, one_mul]
  have second_of_transmission (DE : L2Vector) (G : Fin 3 → Fin 3 → L2Scalar)
      (hG : ∀ t j, HasWeakPartial (Packet05FlatTransmissionH1.transmissionComponent d hd
        (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) j) (G t j) t) :
      ∀ t j, ∃ v, HasPartialOn V (DE j) v t := by
    intro t j
    by_cases hj : j = 2
    · subst j
      have hp : HasWeakPartial (Packet05FlatWeight.mulWeight d hd
          (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (DE 2)))
          (G t 2) t := by simpa [Packet05FlatTransmissionH1.transmissionComponent] using hG t 2
      have hlocal : HasPartialOn V
          (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (DE 2))
          (((ε₀ : ℂ)⁻¹) • G t 2) t :=
        Packet05LocalDerivative.weighted_partial_gives_phase_partial V d hd ε₀ hε₀ hε _ (G t 2) t hp
      exact ⟨_, partial_on_of_ae_eq V _ _ _ t hlocal (hcut (DE 2))⟩
    · have hp : HasWeakPartial (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) (G t j) t := by
        simpa [Packet05FlatTransmissionH1.transmissionComponent, hj] using hG t j
      exact ⟨_, cutoff_partial_on V ζ₁.complexTest.toTest (DE j) (G t j) t hζ₁unit hp⟩
  have hs0 := second_of_transmission DE0 G0 (fun t j => (hG0 t j).1)
  have hs1 := second_of_transmission DE1 G1 (fun t j => (hG1 t j).1)
  have hsecondall : ∀ t i j, ∃ v, HasPartialOn V (deriv i j) v t := by
    intro t i j
    fin_cases i
    · exact hs0 t j
    · exact hs1 t j
    · fin_cases t
      · obtain ⟨v,hv⟩ := hs0 2 j
        exact ⟨v, mixed_partial_on_commute V hVopen (F j) (deriv 0 j) (deriv 2 j) v 0 2
          (hfirst 0 j) (hfirst 2 j) hv⟩
      · obtain ⟨v,hv⟩ := hs1 2 j
        exact ⟨v, mixed_partial_on_commute V hVopen (F j) (deriv 1 j) (deriv 2 j) v 1 2
          (hfirst 1 j) (hfirst 2 j) hv⟩
      · exact ⟨Qv j, hnsecond j⟩
  classical
  choose Hess hHess using hsecondall
  exact ⟨deriv, Hess, hfield, hfirst, hHess⟩

end OQ14.Packet05ActualFlatH2
#print axioms OQ14.Packet05ActualFlatH2.actual_flat_phase_h2

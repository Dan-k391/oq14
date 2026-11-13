import Packet05SecondTangential
import Packet05ActualNormalFlux
import Packet05NormalNormal
import Packet05PartialProduct

/-! Actual phasewise normal-normal derivative from differentiated Maxwell
and the normal displacement equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualNormalNormal
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05SecondTangential
  OQ14.Packet05ActualNormalFlux OQ14.Packet05NormalNormal
open scoped Topology

theorem actual_phase_normal_normal {Ω U : Set Space}
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
    (hε : ∀ x ∈ V, FlatDifferenceCoercivity.dielectric d x = ε₀) :
    ∃ N Q : L2Scalar,
      HasWeakPartial (Packet05FlatWeight.mulWeight d hd
        (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 2))) N 2 ∧
      (∀ φ : Test, tsupport φ.function ⊆ V →
        valuePair φ (((ε₀ : ℂ)⁻¹) • N) + derivativePair φ 2
          (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
            ((LocalPower.cutExtend hΩ κ₀ E).val.1 2)) = 0) ∧
      (∀ φ : Test, tsupport φ.function ⊆ V →
        valuePair φ Q + derivativePair φ 2 (((ε₀ : ℂ)⁻¹) • N) = 0) := by
  obtain ⟨A0,A1,N,hA0,hA1,hN,hflux⟩ :=
    actual_normal_displacement_relation hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
      A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
      L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hU hζunit₀
  have hsecond := actual_second_tangential_derivatives hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
  obtain ⟨DE0,hDE0,_,G0,hG0⟩ := hsecond 0 (by decide)
  obtain ⟨DE1,hDE1,_,G1,hG1⟩ := hsecond 1 (by decide)
  have he0 : A0 = DE0 0 := Packet05LocalDerivative.weak_partial_unique _ A0 (DE0 0) 0 hA0 (hDE0 0)
  have he1 : A1 = DE1 1 := Packet05LocalDerivative.weak_partial_unique _ A1 (DE1 1) 1 hA1 (hDE1 1)
  have hp0 : HasWeakPartial (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
      ζ₁.complexTest.compact A0) (G0 2 0) 2 := by
    rw [he0]
    simpa [Packet05FlatTransmissionH1.transmissionComponent] using (hG0 2 0).1
  have hp1 : HasWeakPartial (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
      ζ₁.complexTest.compact A1) (G1 2 1) 2 := by
    rw [he1]
    simpa [Packet05FlatTransmissionH1.transmissionComponent] using (hG1 2 1).1
  have hfluxV : ∀ᵐ x ∂volume, x ∈ V → N x = -(Packet05FlatWeight.weight d x) * (A0 x + A1 x) := by
    filter_upwards [hflux] with x hx hxV
    exact hx (hVU hxV)
  obtain ⟨hfirst,hsecond⟩ := phase_normal_normal_from_flux V d hd ε₀ hε₀ hε _ N A0 A1
    (G0 2 0) (G1 2 1) ζ₁.complexTest.toTest hζ₁unit hN hfluxV hp0 hp1
  exact ⟨N, -(G0 2 0 + G1 2 1), hN, hfirst, hsecond⟩


theorem actual_phase_tangential_normal_normal {Ω U : Set Space}
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
    (hε : ∀ x ∈ V, FlatDifferenceCoercivity.dielectric d x = ε₀) :
    ∃ N0 Q0 N1 Q1 : L2Scalar,
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ N0 + derivativePair φ 2
        (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 0)) = 0) ∧
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ Q0 + derivativePair φ 2 N0 = 0) ∧
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ N1 + derivativePair φ 2
        (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 1)) = 0) ∧
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ Q1 + derivativePair φ 2 N1 = 0) := by
  have hsecond := actual_second_tangential_derivatives hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
  obtain ⟨DE0,hDE0,_,G0,hG0⟩ := hsecond 0 (by decide)
  obtain ⟨DE1,hDE1,_,G1,hG1⟩ := hsecond 1 (by decide)
  have hball : Metric.ball c₀ r₀ ⊆ Metric.ball c₀ R₀ := Metric.ball_subset_ball hr₀.le
  let χ : DomainCurl.Test Ω := ⟨ζ₀.complexTest.toTest, ζ₀.complexTest.inside.trans (hball.trans hS₀)⟩
  have hχS : tsupport χ.function ⊆ Metric.ball c₀ R₀ := ζ₀.complexTest.inside.trans hball
  let e := LocalPower.cutExtend hΩ χ E
  let h := LocalPower.cutExtend hΩ χ H
  have hnest (j : Fin 3) : e.val.1 j =
      scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
        ((LocalPower.cutExtend hΩ κ₀ E).val.1 j) :=
    Packet05ActualDifferentiatedMaxwell.nested_cutoff_field Ω (Metric.ball c₀ R₀) hΩ κ₀ χ hχS hS₀ hκ₀ E j
  have hloc := Packet05ActualDifferentiatedMaxwell.actual_cutoff_local_maxwell hΩ χ
    (hU.trans (hball.trans hS₀)) hζunit₀ k d hd E H hM
  have hc0 : ∀ᵐ x ∂volume, x ∈ V → e.val.2 0 x = (Complex.I*(k : ℂ)) * h.val.1 0 x := by
    filter_upwards [hloc.1 0] with x hx hxV
    exact hx (hVU hxV)
  have hc1 : ∀ᵐ x ∂volume, x ∈ V → e.val.2 1 x = (Complex.I*(k : ℂ)) * h.val.1 1 x := by
    filter_upwards [hloc.1 1] with x hx hxV
    exact hx (hVU hxV)
  have hD0 : HasWeakPartial (e.val.1 2) (DE0 2) 0 := by rw [hnest 2]; exact hDE0 2
  have hD1 : HasWeakPartial (e.val.1 2) (DE1 2) 1 := by rw [hnest 2]; exact hDE1 2
  have hfirst0 := normal_first_component_from_local_curl V e.val.1 e.val.2 h.val.1
    (Complex.I*(k : ℂ)) (DE0 2) e.property hD0 hc1
  have hfirst1 := normal_second_component_from_local_curl V e.val.1 e.val.2 h.val.1
    (Complex.I*(k : ℂ)) (DE1 2) e.property hD1 hc0
  have hW0 : HasWeakPartial (Packet05FlatWeight.mulWeight d hd
      (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (DE0 2)))
      (G0 2 2) 2 := by
    simpa [Packet05FlatTransmissionH1.transmissionComponent] using (hG0 2 2).1
  have hW1 : HasWeakPartial (Packet05FlatWeight.mulWeight d hd
      (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous ζ₁.complexTest.compact (DE1 2)))
      (G1 2 2) 2 := by
    simpa [Packet05FlatTransmissionH1.transmissionComponent] using (hG1 2 2).1
  have hmixed0 := Packet05LocalDerivative.weighted_partial_gives_phase_partial V d hd ε₀ hε₀ hε _ (G0 2 2) 2 hW0
  have hmixed1 := Packet05LocalDerivative.weighted_partial_gives_phase_partial V d hd ε₀ hε₀ hε _ (G1 2 2) 2 hW1
  obtain ⟨GH,hGH,_⟩ := LocalRegularity.maxwell_cutoff_magnetic_regularity hΩ χ hζ₀2 k hk _ E H hM
  have hmag0 := Packet05PartialProduct.cutoff_weak_partial ζ₁.complexTest.toTest (h.val.1 0) (GH (2,0)) 2 (hGH (2,0))
  have hmag1 := Packet05PartialProduct.cutoff_weak_partial ζ₁.complexTest.toTest (h.val.1 1) (GH (2,1)) 2 (hGH (2,1))
  obtain ⟨N0,Q0,hN0,hQ0⟩ := phase_tangential_normal_normal V (e.val.1 0) (DE0 2) (h.val.1 1)
    (((ε₀ : ℂ)⁻¹) • G0 2 2) _ (Complex.I*(k : ℂ)) ζ₁.complexTest.toTest hζ₁unit hfirst0 hmixed0 hmag1
  have hfirst1' : ∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ (DE1 2) + (-(Complex.I*(k : ℂ))) * valuePair φ (h.val.1 0) + derivativePair φ 2 (e.val.1 1) = 0 := by
    intro φ hφ
    have hh := hfirst1 φ hφ
    linear_combination hh
  obtain ⟨N1,Q1,hN1,hQ1⟩ := phase_tangential_normal_normal V (e.val.1 1) (DE1 2) (h.val.1 0)
    (((ε₀ : ℂ)⁻¹) • G1 2 2) _ (-(Complex.I*(k : ℂ))) ζ₁.complexTest.toTest hζ₁unit hfirst1' hmixed1 hmag0
  refine ⟨N0,Q0,N1,Q1,?_,hQ0,?_,hQ1⟩
  · simpa only [← hnest 0] using hN0
  · simpa only [← hnest 1] using hN1

end OQ14.Packet05ActualNormalNormal
#print axioms OQ14.Packet05ActualNormalNormal.actual_phase_normal_normal
#print axioms OQ14.Packet05ActualNormalNormal.actual_phase_tangential_normal_normal

import Packet05TangentialRegularity
import Packet05LocalDerivative

/-! The constitutive law for actual tangentially differentiated fields on
each flat material phase. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualPhaseDerivatives
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05TangentialRegularity
open scoped Topology

theorem actual_tangential_phase_constitutive {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A) (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r)) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∀ (i : Fin 3), i ≠ 2 → ∀ (j : Fin 3),
      ∃ De Dw : L2Scalar,
        HasWeakPartial (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
          ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)) De i ∧
        HasWeakPartial (Packet05FlatWeight.mulWeight d hd
          (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
            ((LocalPower.cutExtend hΩ κ E).val.1 j))) Dw i ∧
        (∀ᵐ x ∂volume, x 2 < 0 → Dw x = De x) ∧
        (∀ᵐ x ∂volume, 0 < x 2 → Dw x = ((1+d : ℝ) : ℂ) * De x) := by
  intro i hi j
  obtain ⟨De, hDe⟩ := actual_ball_electric_tangential_weak_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi j
  obtain ⟨Dw, hDw⟩ := actual_ball_weighted_electric_tangential_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi j
  refine ⟨De, Dw, hDe, hDw, ?_, ?_⟩
  · have hopen : IsOpen {x : Space | x 2 < 0} :=
      isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const
    have hphase := Packet05LocalDerivative.weighted_partial_on_constant_phase _ hopen d hd 1
      (fun x hx => by
        change x 2 < 0 at hx
        simp [FlatDifferenceCoercivity.dielectric, hx]) _ De Dw i hDe hDw
    filter_upwards [hphase] with x hx hmem
    simpa using hx hmem
  · have hopen : IsOpen {x : Space | 0 < x 2} :=
      isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
    have hphase := Packet05LocalDerivative.weighted_partial_on_constant_phase _ hopen d hd (1+d)
      (fun x hx => by
        change 0 < x 2 at hx
        simp [FlatDifferenceCoercivity.dielectric, not_lt.mpr hx.le]) _ De Dw i hDe hDw
    exact hphase

end OQ14.Packet05ActualPhaseDerivatives
#print axioms OQ14.Packet05ActualPhaseDerivatives.actual_tangential_phase_constitutive

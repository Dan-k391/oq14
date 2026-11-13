import Packet05TangentialRegularity
import Packet05LocalDerivative

/-! Actual local Maxwell divergence recovers the normal displacement
derivative from tangential electric derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualNormalFlux
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05TangentialRegularity
open scoped Topology

theorem actual_normal_displacement_relation {Ω U : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A) (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r))
    (hζ2 : ContDiff ℝ 2 ζ.complexTest.function) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D)
    (hU : U ⊆ Metric.ball c r)
    (hζunit : ∀ x ∈ U, ζ.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ∃ A0 A1 N : L2Scalar,
      HasWeakPartial (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
        ((LocalPower.cutExtend hΩ κ E).val.1 0)) A0 0 ∧
      HasWeakPartial (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
        ((LocalPower.cutExtend hΩ κ E).val.1 1)) A1 1 ∧
      HasWeakPartial (Packet05FlatWeight.mulWeight d hd
        (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 2))) N 2 ∧
      ∀ᵐ x ∂volume, x ∈ U → N x = -(Packet05FlatWeight.weight d x) * (A0 x + A1 x) := by
  let F : L2Vector := fun j => scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
    ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)
  have ht := actual_ball_electric_tangential_weak_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  have hw := actual_ball_weighted_electric_tangential_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  obtain ⟨A0, hA0⟩ := ht 0 (by decide) 0
  obtain ⟨A1, hA1⟩ := ht 1 (by decide) 1
  obtain ⟨B0, hB0⟩ := hw 0 (by decide) 0
  obtain ⟨B1, hB1⟩ := hw 1 (by decide) 1
  obtain ⟨N, hN⟩ := actual_ball_weighted_electric_normal_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ hζ2 η hη hζ L C D hC hgrad hηbound hζder
  have hball : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  let χ : DomainCurl.Test Ω := ⟨ζ.complexTest.toTest, ζ.complexTest.inside.trans (hball.trans hSΩ)⟩
  have hχS : tsupport χ.function ⊆ Metric.ball c R := ζ.complexTest.inside.trans hball
  have hUΩ : U ⊆ Ω := hU.trans (hball.trans hSΩ)
  obtain ⟨Q, hQ, hQeq⟩ := Packet05WeightedDivergence.actual_cutoff_weighted_divergence
    hΩ κ χ hζ2 hχS hSΩ hκ k d hk hd E H hM
  have hsource := Packet05WeightedDivergence.cutoff_divergence_vanishes_on hΩ χ hUΩ hζunit H.val.2
  have hzero : ∀ᵐ x ∂volume, x ∈ U → Q x = 0 := by
    rw [hQeq]
    filter_upwards [hsource, Lp.coeFn_smul (-(Complex.I*(k : ℂ)))⁻¹
      (OQ14.CurlCutoff.extendScalar Ω hΩ.measurableSet (OQ14.LocalRegularity.cutoffDivergence Ω χ.toTest H.val.2))]
      with x hs hm hx
    rw [hm]
    simp only [Pi.smul_apply, smul_eq_mul, hs hx, mul_zero]
  refine ⟨A0, A1, N, hA0, hA1, hN, ?_⟩
  exact Packet05LocalDerivative.normal_displacement_from_divergence U d hd F Q A0 A1 B0 B1 N
    hQ hzero hA0 hA1 hB0 hB1 hN

end OQ14.Packet05ActualNormalFlux
#print axioms OQ14.Packet05ActualNormalFlux.actual_normal_displacement_relation

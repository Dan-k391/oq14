import Packet05DifferenceMaxwell
import Packet05DifferenceConverse
import Packet05CurlNormal
import Packet05WeightedDivergence

/-! Actual flat-interface Maxwell fields have local L² tangential derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TangentialRegularity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.WeakPower OQ14.CurlCutoff
  OQ14.Packet05DifferenceMaxwell OQ14.Packet05DifferenceConverse OQ14.DivCurlCompact
open scoped Topology

theorem actual_ball_electric_tangential_weak_derivative {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A)
    (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
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
      ∃ v : L2Scalar, HasWeakPartial
        (WeakGreen.scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
          ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)) v i := by
  intro i hi j
  let u := WeakGreen.scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
    ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)
  let K := Real.sqrt (3 * (2 + 4 * L ^ 2 / k ^ 2)) * (C *
      (3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
        (3 * B * ‖H.val.1‖)^2 + 1))) +
      3*D*‖(LocalPower.cutExtend hΩ κ E).val.1 j‖
  have hq : ∀ h : ℝ, h ≠ 0 → |h| < R-r → ‖MaxwellDifferenceQuotient.quotient u i h‖ ≤ K :=
    fun h hh hs => actual_ball_cutoff_electric_difference_uniform hΩ c r R hrR.le κ hκ2 hSΩ hκ
      A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi h hh hs j
  have hgap : 0 < R-r := sub_pos.mpr hrR
  have hstep : (R-r)/2 ≠ 0 := ne_of_gt (by linarith)
  have hsmall : |(R-r)/2| < R-r := by rw [abs_of_pos (by linarith)]; linarith
  have hK : 0 ≤ K := (norm_nonneg _).trans (hq _ hstep hsmall)
  obtain ⟨v, hv, _⟩ := weakPartial_of_bounded_quotients u i K (R-r) hK hgap hq
  exact ⟨v, hv⟩

/-- The normal derivatives of the two tangential components follow from
actual curl E and the already established tangential derivatives of E₂. -/
theorem actual_ball_electric_normal_tangential_components {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A)
    (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r)) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∀ j : Fin 3, j ≠ 2 → ∃ v : L2Scalar, HasWeakPartial
      (WeakGreen.scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
        ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)) v 2 := by
  have hT := actual_ball_electric_tangential_weak_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  obtain ⟨D0, h0⟩ := hT 0 (by decide) 2
  obtain ⟨D1, h1⟩ := hT 1 (by decide) 2
  have hn := Packet05CurlNormal.cutoff_normal_tangential_components
    (LocalPower.cutExtend hΩ κ E) ζ.complexTest.toTest D0 D1 h0 h1
  intro j hj
  fin_cases j
  · exact hn.1
  · exact hn.2
  · contradiction

/-- Tangential derivatives also exist after multiplication by the actual
piecewise-constant dielectric, including for the normal field component. -/
theorem actual_ball_weighted_electric_tangential_derivative {Ω : Set Space}
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
    ∀ (i : Fin 3), i ≠ 2 → ∀ (j : Fin 3), ∃ v : L2Scalar, HasWeakPartial
      (Packet05FlatWeight.mulWeight d hd
        (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 j))) v i := by
  intro i hi j
  let u := scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
    ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)
  let K := Real.sqrt (3 * (2 + 4 * L ^ 2 / k ^ 2)) * (C *
      (3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
        (3 * B * ‖H.val.1‖)^2 + 1))) + 3*D*‖(LocalPower.cutExtend hΩ κ E).val.1 j‖
  have hq : ∀ h : ℝ, h ≠ 0 → |h| < R-r → ‖MaxwellDifferenceQuotient.quotient u i h‖ ≤ K :=
    fun h hh hs => actual_ball_cutoff_electric_difference_uniform hΩ c r R hrR.le κ hκ2 hSΩ hκ
      A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi h hh hs j
  have hgap : 0 < R-r := sub_pos.mpr hrR
  have hstep : (R-r)/2 ≠ 0 := ne_of_gt (by linarith)
  have hsmall : |(R-r)/2| < R-r := by rw [abs_of_pos (by linarith)]; linarith
  have hK : 0 ≤ K := (norm_nonneg _).trans (hq _ hstep hsmall)
  obtain ⟨v, hv, _⟩ := Packet05FlatWeight.weighted_weakPartial_of_bounded_quotients
    d hd u i hi K (R-r) hK hgap hq
  exact ⟨v, hv⟩

/-- The weighted normal component has an L² normal derivative across the
interface; no continuity of the unweighted normal field is asserted. -/
theorem actual_ball_weighted_electric_normal_derivative {Ω : Set Space}
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
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∃ v : L2Scalar, HasWeakPartial
      (Packet05FlatWeight.mulWeight d hd
        (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 2))) v 2 := by
  have ht := actual_ball_weighted_electric_tangential_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  obtain ⟨G0, h0⟩ := ht 0 (by decide) 0
  obtain ⟨G1, h1⟩ := ht 1 (by decide) 1
  have hball : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  let χ : DomainCurl.Test Ω := ⟨ζ.complexTest.toTest, ζ.complexTest.inside.trans (hball.trans hSΩ)⟩
  have hχS : tsupport χ.function ⊆ Metric.ball c R := ζ.complexTest.inside.trans hball
  obtain ⟨D', hdiv, _⟩ := Packet05WeightedDivergence.actual_cutoff_weighted_divergence
    hΩ κ χ hζ2 hχS hSΩ hκ k d hk hd E H hM
  exact ⟨D' - G0 - G1, Packet05DivergenceUpgrade.normal_from_divergence _ D' G0 G1 hdiv h0 h1⟩

end OQ14.Packet05TangentialRegularity
#print axioms OQ14.Packet05TangentialRegularity.actual_ball_electric_tangential_weak_derivative
#print axioms OQ14.Packet05TangentialRegularity.actual_ball_electric_normal_tangential_components
#print axioms OQ14.Packet05TangentialRegularity.actual_ball_weighted_electric_tangential_derivative
#print axioms OQ14.Packet05TangentialRegularity.actual_ball_weighted_electric_normal_derivative

import Packet05ActualDifferentiatedMaxwell
import Packet05FlatTransmissionH1

/-! Reapply the actual Maxwell tangential regularity theorem to the regional
differentiated fields, with exact nested-cutoff identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05SecondTangential
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05DifferenceMaxwell
  OQ14.Packet05TangentialRegularity OQ14.Packet05ActualDifferentiatedMaxwell
open scoped Topology

theorem nested_scale (χ η : Test) (u : L2Scalar)
    (hη : ∀ x ∈ tsupport χ.function, η.function x = 1) :
    scaleL2 χ.function χ.regular.continuous χ.compact
      (scaleL2 η.function η.regular.continuous η.compact u) =
    scaleL2 χ.function χ.regular.continuous χ.compact u := by
  apply Lp.ext
  filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact
      (scaleL2 η.function η.regular.continuous η.compact u),
    scaleL2_ae η.function η.regular.continuous η.compact u,
    scaleL2_ae χ.function χ.regular.continuous χ.compact u] with x h1 h2 h3
  rw [h1, h2, h3]
  by_cases hx : x ∈ tsupport χ.function
  · rw [hη x hx]
    simp
  · rw [image_eq_zero_of_nmem_tsupport hx]
    simp

/-- Given a regional Maxwell pair whose electric component is a known actual
L² field F, every tangential partial of a smaller cutoff of F is in L². -/
theorem second_stage_regional_tangential {U : Set Space} (hU : IsOpen U)
    (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test U) (hκ2 : ContDiff ℝ 2 κ.function)
    (hS : Metric.ball c R ⊆ U)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A) (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl U)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H) (F : L2Vector)
    (hF : ∀ j, (fun x => E.val.1 j x) =ᵐ[DomainCurl.regionMeasure U] fun x => F j x)
    (ζ : WeakConservation.RealTest (Metric.ball c r)) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∀ (i : Fin 3), i ≠ 2 → ∀ j : Fin 3, ∃ v : L2Scalar,
      HasWeakPartial (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
        ζ.complexTest.compact (F j)) v i := by
  have ht := actual_ball_electric_tangential_weak_derivative hU c r R hrR κ hκ2 hS hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  have hnest (j : Fin 3) : (LocalPower.cutExtend hU κ E).val.1 j =
      scaleL2 κ.function κ.regular.continuous κ.compact (F j) :=
    cutField_global_ae hU κ (E.val.1 j) (F j) (hF j)
  have hon : ∀ x ∈ tsupport ζ.complexTest.function, κ.function x = 1 := by
    intro x hx
    have hxr : x ∈ Metric.ball c r := ζ.complexTest.inside hx
    exact (hκ x (Metric.ball_subset_ball hrR.le hxr)).self_of_nhds
  intro i hi j
  obtain ⟨v, hv⟩ := ht i hi j
  rw [hnest j, nested_scale ζ.complexTest.toTest κ.toTest (F j) hon] at hv
  exact ⟨v, hv⟩

/-- Actual flat-interface Maxwell fields have second tangential weak
derivatives on a smaller cutoff, obtained by differentiating Maxwell and
reapplying the proved first-order estimate. -/
theorem actual_second_tangential_derivatives {Ω U : Set Space}
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
    (hζder₁ : ∀ l x, ‖dcoord ζ₁.complexTest.function x l‖ ≤ D₁) :
    ∀ (i : Fin 3), i ≠ 2 → ∃ DE : L2Vector,
      (∀ j, HasWeakPartial
        (scaleL2 ζ₀.complexTest.function ζ₀.complexTest.regular.continuous ζ₀.complexTest.compact
          ((LocalPower.cutExtend hΩ κ₀ E).val.1 j)) (DE j) i) ∧
      (∀ (t : Fin 3), t ≠ 2 → ∀ j : Fin 3, ∃ v : L2Scalar,
        HasWeakPartial (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) v t) ∧
      (∃ G : Fin 3 → Fin 3 → L2Scalar, ∀ t j,
        HasWeakPartial (Packet05FlatTransmissionH1.transmissionComponent d hd
          (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
            ζ₁.complexTest.compact (DE j)) j) (G t j) t ∧
        (j = 2 → ∀ φ : Test, tsupport φ.function ⊆ {x : Space | x 2 < 0} →
          valuePair φ (G t j) + derivativePair φ t
            (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
              ζ₁.complexTest.compact (DE j)) = 0) ∧
        (j = 2 → ∀ φ : Test, tsupport φ.function ⊆ {x : Space | 0 < x 2} →
          valuePair φ (((((1+d : ℝ) : ℂ)⁻¹)) • G t j) + derivativePair φ t
            (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
              ζ₁.complexTest.compact (DE j)) = 0)) := by
  intro i hi
  obtain ⟨DE, DH, DW, hDE, _, _, _, E', H', hE', _, hmax⟩ :=
    actual_tangential_differentiated_maxwell hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
      A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
      L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀ i hi
  refine ⟨DE, hDE, ?_, ?_⟩
  · exact second_stage_regional_tangential hUopen c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁
      A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁ k d hk hd E' H' hmax DE hE' ζ₁ η₁ hη₁ hζ₁
      L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
  · obtain ⟨G, hG⟩ := Packet05FlatTransmissionH1.actual_flat_transmission_h1
      hUopen c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
      k d hk hd E' H' hmax ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
    have hon : ∀ x ∈ tsupport ζ₁.complexTest.function, κ₁.function x = 1 := by
      intro x hx
      have hxr : x ∈ Metric.ball c₁ r₁ := ζ₁.complexTest.inside hx
      exact (hκ₁ x (Metric.ball_subset_ball hr₁.le hxr)).self_of_nhds
    have heq : (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
        ζ₁.complexTest.compact ((LocalPower.cutExtend hUopen κ₁ E').val.1 j)) =
        (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) := by
      funext j
      rw [show (LocalPower.cutExtend hUopen κ₁ E').val.1 j =
        scaleL2 κ₁.function κ₁.regular.continuous κ₁.compact (DE j) from
          cutField_global_ae hUopen κ₁ (E'.val.1 j) (DE j) (hE' j)]
      exact nested_scale ζ₁.complexTest.toTest κ₁.toTest (DE j) hon
    have hG' : ∀ t j, HasWeakPartial (Packet05FlatTransmissionH1.transmissionComponent d hd
        (fun j => scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
          ζ₁.complexTest.compact (DE j)) j) (G t j) t := by
      rw [← heq]
      exact hG
    refine ⟨G, ?_⟩
    intro t j
    refine ⟨hG' t j, ?_, ?_⟩
    · intro hj φ hφ
      subst j
      have hpartial : HasWeakPartial (Packet05FlatWeight.mulWeight d hd
          (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
            ζ₁.complexTest.compact (DE 2))) (G t 2) t := by
        simpa [Packet05FlatTransmissionH1.transmissionComponent] using hG' t 2
      have hx := Packet05LocalDerivative.weighted_partial_gives_phase_partial
        {x : Space | x 2 < 0} d hd 1 (by norm_num)
        (fun x hx => by change x 2 < 0 at hx; simp [FlatDifferenceCoercivity.dielectric, hx])
        _ (G t 2) t hpartial φ hφ
      simpa using hx
    · intro hj φ hφ
      subst j
      have hpartial : HasWeakPartial (Packet05FlatWeight.mulWeight d hd
          (scaleL2 ζ₁.complexTest.function ζ₁.complexTest.regular.continuous
            ζ₁.complexTest.compact (DE 2))) (G t 2) t := by
        simpa [Packet05FlatTransmissionH1.transmissionComponent] using hG' t 2
      have hpos : (1+d : ℝ) ≠ 0 := ne_of_gt (by linarith)
      exact Packet05LocalDerivative.weighted_partial_gives_phase_partial
        {x : Space | 0 < x 2} d hd (1+d) hpos
        (fun x hx => by change 0 < x 2 at hx; simp [FlatDifferenceCoercivity.dielectric, not_lt.mpr hx.le])
        _ (G t 2) t hpartial φ hφ

end OQ14.Packet05SecondTangential
#print axioms OQ14.Packet05SecondTangential.nested_scale
#print axioms OQ14.Packet05SecondTangential.second_stage_regional_tangential
#print axioms OQ14.Packet05SecondTangential.actual_second_tangential_derivatives

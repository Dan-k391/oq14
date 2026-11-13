import MaxwellInverseCurlCurl

/-! Full local electric H1 on a constant, nonzero material phase. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PhaseRegularity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.DivCurlRegularity OQ14.CurlCutoff
open scoped Topology

theorem constant_phase_electric_divergence {Ω : Set Space}
    (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : ε₀ ≠ 0) (ε : Space → ℝ)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x = ε₀)
    (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    DomainCurl.DivergenceFree Ω E.val.1 := by
  intro f hf hc hi
  have hh := DomainCurl.weak_divergence_curl Ω H.property f hf hc hi
  have he (j : Fin 3) :
      (∫ x in Ω, H.val.2 j x * dcoord f x j) =
        (-(Complex.I * (k : ℂ)) * (ε₀ : ℂ)) *
          (∫ x in Ω, E.val.1 j x * dcoord f x j) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hM.2, hε] with x hx hxe
    rw [hx j, hxe]
    ring
  rw [he 0, he 1, he 2] at hh
  have hn : -(Complex.I * (k : ℂ)) * (ε₀ : ℂ) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)))
      (Complex.ofReal_ne_zero.mpr hε₀)
  apply (mul_eq_zero.mp ?_).resolve_left hn
  linear_combination hh

/-- All nine weak L2 derivatives are obtained for an arbitrary compact
interior cutoff, including the normal component and normal direction. -/
theorem constant_phase_electric_cutoff_h1 {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : ε₀ ≠ 0) (ε : Space → ℝ)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x = ε₀)
    (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) =
        (∑ j, ‖extendVector Ω hΩ.measurableSet
          (productCurl Ω χ.toTest E.val.1 E.val.2) j‖ ^ 2) +
        ‖extendScalar Ω hΩ.measurableSet (LocalRegularity.cutoffDivergence Ω χ.toTest E.val.1)‖ ^ 2 := by
  exact LocalRegularity.cutoff_divcurl_regularity hΩ χ hχ E
    (constant_phase_electric_divergence k ε₀ hk hε₀ ε hε E H hM)

/-- The same phase result for genuine regional H(curl) fields at a nonzero
complex frequency, with the Maxwell curl equation exposed explicitly. -/
theorem complex_constant_phase_electric_cutoff_h1 {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (z ε₀ : ℂ) (hz : z ≠ 0) (hε₀ : ε₀ ≠ 0)
    (E H : DomainCurl.HCurl Ω)
    (hcurl : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      H.val.2 j x = -(Complex.I * z * ε₀) * E.val.1 j x) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) =
        (∑ j, ‖extendVector Ω hΩ.measurableSet
          (productCurl Ω χ.toTest E.val.1 E.val.2) j‖ ^ 2) +
        ‖extendScalar Ω hΩ.measurableSet (LocalRegularity.cutoffDivergence Ω χ.toTest E.val.1)‖ ^ 2 := by
  have hdiv : DomainCurl.DivergenceFree Ω E.val.1 := by
    intro f hf hc hi
    have hh := DomainCurl.weak_divergence_curl Ω H.property f hf hc hi
    have he (j : Fin 3) :
        (∫ x in Ω, H.val.2 j x * dcoord f x j) =
          (-(Complex.I * z * ε₀)) * (∫ x in Ω, E.val.1 j x * dcoord f x j) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcurl] with x hx
      rw [hx j]
      ring
    rw [he 0, he 1, he 2] at hh
    have hn : -(Complex.I * z * ε₀) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero Complex.I_ne_zero hz) hε₀)
    apply (mul_eq_zero.mp ?_).resolve_left hn
    linear_combination hh
  exact LocalRegularity.cutoff_divcurl_regularity hΩ χ hχ E hdiv

/-- Magnetic H1 holds across any interface for actual regional complex
Maxwell fields when permeability is constant and frequency is nonzero. -/
theorem complex_magnetic_cutoff_h1 {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (z : ℂ) (hz : z ≠ 0) (E H : DomainCurl.HCurl Ω)
    (hcurl : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
      E.val.2 j x = (Complex.I * z) * H.val.1 j x) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) =
        (∑ j, ‖extendVector Ω hΩ.measurableSet
          (productCurl Ω χ.toTest H.val.1 H.val.2) j‖ ^ 2) +
        ‖extendScalar Ω hΩ.measurableSet (LocalRegularity.cutoffDivergence Ω χ.toTest H.val.1)‖ ^ 2 := by
  have hdiv : DomainCurl.DivergenceFree Ω H.val.1 := by
    intro f hf hc hi
    have hh := DomainCurl.weak_divergence_curl Ω E.property f hf hc hi
    have he (j : Fin 3) :
        (∫ x in Ω, E.val.2 j x * dcoord f x j) =
          (Complex.I * z) * (∫ x in Ω, H.val.1 j x * dcoord f x j) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcurl] with x hx
      rw [hx j]
      ring
    rw [he 0, he 1, he 2] at hh
    have hn : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
    apply (mul_eq_zero.mp ?_).resolve_left hn
    linear_combination hh
  exact LocalRegularity.cutoff_divcurl_regularity hΩ χ hχ H hdiv

end OQ14.Packet05PhaseRegularity
#print axioms OQ14.Packet05PhaseRegularity.constant_phase_electric_divergence
#print axioms OQ14.Packet05PhaseRegularity.constant_phase_electric_cutoff_h1
#print axioms OQ14.Packet05PhaseRegularity.complex_constant_phase_electric_cutoff_h1
#print axioms OQ14.Packet05PhaseRegularity.complex_magnetic_cutoff_h1

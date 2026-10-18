import WeakPoynting.Energy

/-! # Actual support-localized Maxwell electric-energy estimate -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.EnergyLocalization

open MeasureTheory OQ14.Maxwell OQ14.WeakConservation OQ14.WeakEnergy Filter
open scoped Topology

theorem gradient_zero_off_support {Ω : Set Space} (ζ : RealTest Ω) (x : Space)
    (hx : x ∉ tsupport ζ.function) : gradient ζ x = 0 := by
  funext j
  simp [OQ14.WeakEnergy.gradient, fderiv_of_not_mem_tsupport ℝ hx]

theorem cutoff_energy_support_bounds {Ω : Set Space} (ζ : RealTest Ω)
    (u : DomainCurl.L2Vector Ω) (hζ : ∀ x, ‖ζ.function x‖ ≤ 1)
    (d : ℝ) (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2) :
    (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => u j x)) ≤
      (∫ x in tsupport ζ.function, energy (fun j => u j x) ∂DomainCurl.regionMeasure Ω) ∧
    (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => u j x)) ≤
      d ^ 2 * (∫ x in tsupport ζ.function, energy (fun j => u j x) ∂DomainCurl.regionMeasure Ω) := by
  have hs : MeasurableSet (tsupport ζ.function) := isClosed_closure.measurableSet
  have hi := (energy_integrable u).indicator hs
  have hsq (x : Space) : ζ.function x ^ 2 ≤ 1 := by
    have ha : |ζ.function x| ≤ 1 := by simpa only [Real.norm_eq_abs] using hζ x
    exact (sq_le_one_iff_abs_le_one _).mpr ha
  constructor
  · have hm := integral_mono_ae (weighted_energy_integrable (squareTest ζ) u) hi
      (Eventually.of_forall (fun x => by
        by_cases hx : x ∈ tsupport ζ.function
        · rw [Set.indicator_of_mem hx]
          exact mul_le_of_le_one_left (energy_nonneg _) (hsq x)
        · rw [Set.indicator_of_not_mem hx]
          simp [squareTest, image_eq_zero_of_nmem_tsupport hx]))
    rw [integral_indicator hs] at hm
    exact hm
  · have hm := integral_mono_ae (gradient_energy_integrable ζ u) (hi.const_mul (d ^ 2))
      (Eventually.of_forall (fun x => by
        dsimp only
        by_cases hx : x ∈ tsupport ζ.function
        · rw [Set.indicator_of_mem hx]
          exact mul_le_mul_of_nonneg_right (hd x) (energy_nonneg _)
        · rw [Set.indicator_of_not_mem hx, gradient_zero_off_support ζ x hx]
          simp [realEnergy]))
    rw [integral_const_mul, integral_indicator hs] at hm
    exact hm

theorem electric_energy_on_unit_region {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : MeasurableSet K) (ζ : RealTest Ω) (hζK : ∀ x ∈ K, ζ.function x = 1)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, 0 ≤ ε x) :
    IntegrableOn (fun x => ε x * energy (fun j => E.val.1 j x)) K (DomainCurl.regionMeasure Ω) ∧
      (∫ x in K, ε x * energy (fun j => E.val.1 j x) ∂DomainCurl.regionMeasure Ω) ≤
        (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) := by
  have he := weighted_electric_integrable hΩ (squareTest ζ) ω hω ε E H hM
  have heq : (K.indicator (fun x => (squareTest ζ).function x * ε x *
      energy (fun j => E.val.1 j x))) =
      K.indicator (fun x => ε x * energy (fun j => E.val.1 j x)) := by
    funext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx, squareTest, hζK x hx]
    · simp [Set.indicator_of_not_mem hx]
  have hi : Integrable (K.indicator (fun x => ε x * energy (fun j => E.val.1 j x)))
      (DomainCurl.regionMeasure Ω) := by
    rw [← heq]
    exact he.indicator hK
  refine ⟨(integrable_indicator_iff hK).mp hi, ?_⟩
  rw [← integral_indicator hK]
  apply integral_mono_ae hi he
  filter_upwards [hε] with x hxε
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx, squareTest, hζK x hx]
  · rw [Set.indicator_of_not_mem hx]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hxε) (energy_nonneg _)

/-- The manuscript's local electric-to-magnetic energy estimate, with actual
Maxwell fields and an actual cutoff, follows from the proved weighted estimate. -/
theorem maxwell_local_electric_energy {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : MeasurableSet K) (ζ : RealTest Ω) (hζK : ∀ x ∈ K, ζ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) (m : ℝ) (hm : 0 < m)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x) :
    (∫ x in K, ε x * energy (fun j => E.val.1 j x) ∂DomainCurl.regionMeasure Ω) ≤
      (2 + 4 * d ^ 2 / (ω ^ 2 * m)) *
        (∫ x in tsupport ζ.function, energy (fun j => H.val.1 j x) ∂DomainCurl.regionMeasure Ω) := by
  have hzero := hε.mono (fun x hx => hm.le.trans hx)
  have hleft := (electric_energy_on_unit_region hΩ hK ζ hζK ω hω ε E H hM hzero).2
  have hmain := caccioppoli hΩ ζ ω hω ε E H hM m hm hε
  obtain ⟨hB, hG⟩ := cutoff_energy_support_bounds ζ H.val.1 hζ d hd
  have hcoef : 0 ≤ 4 / (ω ^ 2 * m) := by positivity
  calc
    _ ≤ _ := hleft.trans hmain
    _ ≤ 2 * (∫ x in tsupport ζ.function, energy (fun j => H.val.1 j x) ∂DomainCurl.regionMeasure Ω) +
        4 / (ω ^ 2 * m) * (d ^ 2 *
          (∫ x in tsupport ζ.function, energy (fun j => H.val.1 j x) ∂DomainCurl.regionMeasure Ω)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num))
        (mul_le_mul_of_nonneg_left hG hcoef)
    _ = _ := by ring

end OQ14.EnergyLocalization

#print axioms OQ14.EnergyLocalization.gradient_zero_off_support
#print axioms OQ14.EnergyLocalization.cutoff_energy_support_bounds
#print axioms OQ14.EnergyLocalization.electric_energy_on_unit_region
#print axioms OQ14.EnergyLocalization.maxwell_local_electric_energy

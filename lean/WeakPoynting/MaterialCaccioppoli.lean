import WeakPoynting.ElectricControl

/-! # Local magnetic and electric-curl control by electric energy

The complementary Caccioppoli estimate is derived from the actual weak
Maxwell energy identity. No positive lower bound or derivative of the real
permittivity is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaterialCaccioppoli

open MeasureTheory OQ14.Maxwell OQ14.WeakConservation OQ14.WeakEnergy
  OQ14.ElectricControl OQ14.EnergyLocalization Filter
open scoped Topology ComplexConjugate

theorem reactive_swap (g : Fin 3 → ℝ) (E H : Vector) :
    (dot (realLift g) (crossProduct H (conjugate E))).im =
      (dot (realLift g) (crossProduct E (conjugate H))).im := by
  simp [dot, realLift, conjugate, cross_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Actual magnetic energy is controlled by electric energy and the cutoff
gradient, directly from the weak Maxwell graph equations. -/
theorem magnetic_caccioppoli {Ω : Set Space} (hΩ : IsOpen Ω) (ζ : RealTest Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) :
    (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) ≤
      2 * (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) +
        4 / ω ^ 2 *
          (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => E.val.1 j x)) := by
  have he := weighted_electric_integrable hΩ (squareTest ζ) ω hω ε E H hM
  have hh := weighted_energy_integrable (squareTest ζ) H.val.1
  have hr := reactiveFlux_integrable (squareTest ζ) E.val.1 H.val.1
  have hg := gradient_energy_integrable ζ E.val.1
  have hb := weighted_energy_balance hΩ (squareTest ζ) ω hω ε E H hM
  dsimp only [squareTest] at he hh hb
  have hp : ∀ᵐ x ∂DomainCurl.regionMeasure Ω,
      (-2 * ω) * reactiveFlux (squareTest ζ) (fun y j => E.val.1 j y)
        (fun y j => H.val.1 j y) x ≤
      ω ^ 2 * (ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) +
        4 * (realEnergy (gradient ζ x) * energy (fun j => E.val.1 j x)) := by
    filter_upwards with x
    rw [squareTest_reactive]
    have hy := cutoff_young_scaled (-ω) 1 (ζ.function x) (gradient ζ x)
      (fun j => H.val.1 j x) (fun j => E.val.1 j x)
    rw [reactive_swap] at hy
    nlinarith
  have hi := integral_mono_ae (hr.const_mul (-2 * ω))
    ((hh.const_mul (ω ^ 2)).add (hg.const_mul 4)) hp
  dsimp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hh.const_mul (ω ^ 2)) (hg.const_mul 4),
    integral_const_mul, integral_const_mul] at hi
  have hb2 := congrArg (fun r : ℝ => 2 * ω * r) hb
  dsimp only [DomainCurl.regionMeasure, squareTest] at hi hb2
  have hpos : 0 < ω ^ 2 := sq_pos_of_ne_zero hω
  have hs : ω ^ 2 * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) ≤
      ω ^ 2 * (2 * (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x))) +
        4 * (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => E.val.1 j x)) := by
    nlinarith [hi, hb2]
  apply (mul_le_mul_left hpos).mp
  calc
    _ ≤ _ := hs
    _ = _ := by field_simp; ring

theorem electric_curl_energy_ae {Ω : Set Space}
    (ω : ℝ) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) :
    (fun x => energy (fun j => E.val.2 j x)) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => ω ^ 2 * energy (fun j => H.val.1 j x)) := by
  filter_upwards [hM.1] with x hx
  simp only [energy, hx, Complex.ofReal_one, mul_one, map_mul, Complex.normSq_I,
    one_mul, Complex.normSq_ofReal]
  ring

/-- The standard local electric-curl energy estimate, with the curl supplied
by the genuine regional H(curl) graph, rather than a differentiable field. -/
theorem electric_curl_caccioppoli {Ω : Set Space} (hΩ : IsOpen Ω) (ζ : RealTest Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω (fun _ => 1) ε E H) :
    (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => E.val.2 j x)) ≤
      2 * ω ^ 2 * (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) +
        4 * (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => E.val.1 j x)) := by
  have he : (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => E.val.2 j x)) =
      ω ^ 2 * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [electric_curl_energy_ae ω ε E H hM] with x hx
    rw [hx]
    ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left (magnetic_caccioppoli hΩ ζ ω hω ε E H hM)
    (sq_nonneg ω)
  convert hb using 1
  field_simp
  ring

theorem magnetic_cutoff_energy_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (M : ℝ) (hM : 0 ≤ M)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x ≤ M) :
    (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest H.val.1 j‖ ^ 2) ≤
      (2 * M + 4 * d ^ 2 / ω ^ 2) *
        (∑ j : Fin 3, ‖cutField hΩ χ E.val.1 j‖ ^ 2) := by
  have hu : (∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x)) ≤
      M * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => E.val.1 j x)) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (weighted_electric_integrable hΩ (squareTest ζ) ω hω ε E H hMax)
      ((weighted_energy_integrable (squareTest ζ) E.val.1).const_mul M)
    filter_upwards [hε] with x hx
    dsimp [squareTest]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx)
      (mul_nonneg (sq_nonneg (ζ.function x)) (energy_nonneg (fun j => E.val.1 j x)))]
  have hc := magnetic_caccioppoli hΩ ζ ω hω ε E H hMax
  obtain ⟨hB, hG⟩ := cutoff_energy_support_bounds ζ E.val.1 hζ d hd
  have hs := unit_support_energy_le hΩ isClosed_closure.measurableSet χ hχ E.val.1
  rw [real_cutField_energy]
  calc
    _ ≤ _ := hc
    _ ≤ (2 * M + 4 * d ^ 2 / ω ^ 2) *
        (∫ x in tsupport ζ.function, energy (fun j => E.val.1 j x)
          ∂DomainCurl.regionMeasure Ω) := by
      have h := add_le_add
        (mul_le_mul_of_nonneg_left
          (hu.trans (mul_le_mul_of_nonneg_left hB hM)) (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 4 / ω ^ 2))
      convert h using 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

theorem magnetic_cutoff_norm_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (M : ℝ) (hM : 0 ≤ M)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x ≤ M) :
    ‖cutField hΩ ζ.complexTest H.val.1‖ ≤
      Real.sqrt (3 * (2 * M + 4 * d ^ 2 / ω ^ 2)) * ‖cutField hΩ χ E.val.1‖ := by
  have h := magnetic_cutoff_energy_control hΩ ζ χ hχ hζ d hd ω hω ε E H hMax M hM hε
  have he := (vector_energy_bounds (cutField hΩ χ E.val.1)).2
  have hh := (vector_energy_bounds (cutField hΩ ζ.complexTest H.val.1)).1
  let C := 2 * M + 4 * d ^ 2 / ω ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : ‖cutField hΩ ζ.complexTest H.val.1‖ ^ 2 ≤
      (3 * C) * ‖cutField hΩ χ E.val.1‖ ^ 2 := by
    have hu := mul_le_mul_of_nonneg_left he hC
    change _ ≤ C * _ at h
    calc
      _ ≤ _ := (hh.trans h).trans hu
      _ = _ := by ring
  have hCs : 0 ≤ 3 * C := by positivity
  change _ ≤ Real.sqrt (3 * C) * _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt hCs] using hs

/-- A quantitative local bound for the actual weak electric curl using only
an outer electric L2 cutoff. -/
theorem electric_curl_cutoff_energy_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (M : ℝ) (hM : 0 ≤ M)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x ≤ M) :
    (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.2 j‖ ^ 2) ≤
      (2 * ω ^ 2 * M + 4 * d ^ 2) *
        (∑ j : Fin 3, ‖cutField hΩ χ E.val.1 j‖ ^ 2) := by
  have he : (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.2 j‖ ^ 2) =
      ω ^ 2 * (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest H.val.1 j‖ ^ 2) := by
    rw [real_cutField_energy, real_cutField_energy, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [electric_curl_energy_ae ω ε E H hMax] with x hx
    rw [hx]
    ring
  rw [he]
  have hb := mul_le_mul_of_nonneg_left
    (magnetic_cutoff_energy_control hΩ ζ χ hχ hζ d hd ω hω ε E H hMax M hM hε)
    (sq_nonneg ω)
  have hc : ω ^ 2 * (2 * M + 4 * d ^ 2 / ω ^ 2) = 2 * ω ^ 2 * M + 4 * d ^ 2 := by
    field_simp
    ring
  calc
    _ ≤ _ := hb
    _ = _ := by rw [← mul_assoc, hc]

/-- Interior electric field and genuine electric curl energy are controlled
by one outer electric L2 norm. These are local graph quantities; the statement
does not identify the cutoff of curl E with the curl of the cutoff field. -/
theorem electric_local_graph_energy_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (M : ℝ) (hM : 0 ≤ M)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ε x ≤ M) :
    (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.1 j‖ ^ 2) +
        (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.2 j‖ ^ 2) ≤
      (1 + 2 * ω ^ 2 * M + 4 * d ^ 2) *
        (∑ j : Fin 3, ‖cutField hΩ χ E.val.1 j‖ ^ 2) := by
  have hc := electric_curl_cutoff_energy_control hΩ ζ χ hχ hζ d hd ω hω ε E H hMax M hM hε
  have hv : (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.1 j‖ ^ 2) ≤
      ∑ j : Fin 3, ‖cutField hΩ χ E.val.1 j‖ ^ 2 := by
    rw [real_cutField_energy]
    exact (cutoff_energy_support_bounds ζ E.val.1 hζ d hd).1.trans
      (unit_support_energy_le hΩ isClosed_closure.measurableSet χ hχ E.val.1)
  nlinarith [add_le_add hv hc]

end OQ14.MaterialCaccioppoli

#print axioms OQ14.MaterialCaccioppoli.reactive_swap
#print axioms OQ14.MaterialCaccioppoli.magnetic_caccioppoli
#print axioms OQ14.MaterialCaccioppoli.electric_curl_energy_ae
#print axioms OQ14.MaterialCaccioppoli.electric_curl_caccioppoli
#print axioms OQ14.MaterialCaccioppoli.magnetic_cutoff_energy_control
#print axioms OQ14.MaterialCaccioppoli.magnetic_cutoff_norm_control
#print axioms OQ14.MaterialCaccioppoli.electric_curl_cutoff_energy_control
#print axioms OQ14.MaterialCaccioppoli.electric_local_graph_energy_control

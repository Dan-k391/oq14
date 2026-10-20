import WeakPoynting.MagneticCompactness
import WeakPoynting.EnergyLocalization

/-! # Actual local electric L2 control by magnetic L2 energy -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ElectricControl

open MeasureTheory OQ14.Maxwell OQ14.CurlCutoff OQ14.WeakConservation
  OQ14.WeakEnergy OQ14.EnergyLocalization Filter
open scoped Topology InnerProductSpace ComplexConjugate

def cutField {Ω : Set Space} (hΩ : IsOpen Ω) (χ : DomainCurl.Test Ω)
    (u : DomainCurl.L2Vector Ω) : WeakCurl.L2Vector :=
  extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest u)

theorem regional_scalar_norm_squared {Ω : Set Space} (u : DomainCurl.L2Scalar Ω) :
    ‖u‖ ^ 2 = ∫ x in Ω, Complex.normSq (u x) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) u u
  calc
    _ = (⟪u, u⟫_ℂ).re := by
      simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    _ = ∫ x in Ω, (inner (𝕜 := ℂ) (u x) (u x)).re := by
      rw [L2.inner_def, ← RCLike.re_eq_complex_re, ← integral_re hi]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, Complex.normSq_apply])

theorem regional_vector_norm_squared {Ω : Set Space} (u : DomainCurl.L2Vector Ω) :
    (∑ j : Fin 3, ‖u j‖ ^ 2) = ∫ x in Ω, energy (fun j => u j x) := by
  have hi (j : Fin 3) : Integrable (fun x => Complex.normSq (u j x))
      (DomainCurl.regionMeasure Ω) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (u j) (u j)).re.congr
    exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, Complex.normSq_apply])
  simp_rw [regional_scalar_norm_squared]
  rw [← integral_finset_sum _ (fun j _ => hi j)]
  simp only [Fin.sum_univ_three, energy]

theorem multiply_energy_ae {Ω : Set Space} (χ : DomainCurl.Test Ω)
    (u : DomainCurl.L2Vector Ω) :
    (fun x => energy (fun j => multiply Ω χ.toTest u j x)) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => Complex.normSq (χ.function x) * energy (fun j => u j x)) := by
  have hm := ae_all_iff.mpr (fun j =>
    mulL2_ae Ω χ.function χ.regular.continuous χ.compact (u j))
  filter_upwards [hm] with x hx
  change energy (fun j => mulL2 Ω χ.function χ.regular.continuous χ.compact (u j) x) = _
  simp only [energy, hx, Complex.normSq_mul]
  ring

theorem cutoff_energy_integrable {Ω : Set Space} (χ : DomainCurl.Test Ω)
    (u : DomainCurl.L2Vector Ω) :
    Integrable (fun x => Complex.normSq (χ.function x) * energy (fun j => u j x))
      (DomainCurl.regionMeasure Ω) :=
  (energy_integrable (multiply Ω χ.toTest u)).congr (multiply_energy_ae χ u)

theorem cutField_energy {Ω : Set Space} (hΩ : IsOpen Ω) (χ : DomainCurl.Test Ω)
    (u : DomainCurl.L2Vector Ω) :
    (∑ j : Fin 3, ‖cutField hΩ χ u j‖ ^ 2) =
      ∫ x in Ω, Complex.normSq (χ.function x) * energy (fun j => u j x) := by
  change (∑ j : Fin 3, ‖extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest u j)‖ ^ 2) = _
  simp_rw [extendScalar_norm]
  rw [regional_vector_norm_squared, integral_congr_ae (multiply_energy_ae χ u)]

theorem real_cutField_energy {Ω : Set Space} (hΩ : IsOpen Ω) (ζ : RealTest Ω)
    (u : DomainCurl.L2Vector Ω) :
    (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest u j‖ ^ 2) =
      ∫ x in Ω, ζ.function x ^ 2 * energy (fun j => u j x) := by
  rw [cutField_energy]
  apply integral_congr_ae
  filter_upwards with x
  simp [RealTest.complexTest, Complex.normSq_apply, pow_two]

theorem unit_support_energy_le {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : MeasurableSet K) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ K, χ.function x = 1) (u : DomainCurl.L2Vector Ω) :
    (∫ x in K, energy (fun j => u j x) ∂DomainCurl.regionMeasure Ω) ≤
      ∑ j : Fin 3, ‖cutField hΩ χ u j‖ ^ 2 := by
  rw [cutField_energy, ← integral_indicator hK]
  apply integral_mono_ae ((energy_integrable u).indicator hK) (cutoff_energy_integrable χ u)
  filter_upwards with x
  by_cases hx : x ∈ K
  · simp [Set.indicator_of_mem hx, hχ x hx]
  · rw [Set.indicator_of_not_mem hx]
    exact mul_nonneg (Complex.normSq_nonneg _) (energy_nonneg _)

theorem vector_energy_bounds (u : WeakCurl.L2Vector) :
    ‖u‖ ^ 2 ≤ (∑ j : Fin 3, ‖u j‖ ^ 2) ∧
      (∑ j : Fin 3, ‖u j‖ ^ 2) ≤ 3 * ‖u‖ ^ 2 := by
  let S := ∑ j : Fin 3, ‖u j‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hS
  constructor
  · have hn : ‖u‖ ≤ Real.sqrt S := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro j
      have hj : ‖u j‖ ^ 2 ≤ S :=
        Finset.single_le_sum (fun i _ => sq_nonneg ‖u i‖) (Finset.mem_univ j)
      nlinarith [norm_nonneg (u j), Real.sqrt_nonneg S]
    nlinarith [norm_nonneg u, Real.sqrt_nonneg S]
  · have hb (j : Fin 3) := pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm u j) 2
    simp only [Fin.sum_univ_three]
    linarith [hb 0, hb 1, hb 2]

/-- The full actual cutoff electric energy is controlled by an outer magnetic
cutoff that is one on the inner cutoff support. -/
theorem electric_cutoff_energy_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (m : ℝ) (hm : 0 < m)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x) :
    m * (∑ j : Fin 3, ‖cutField hΩ ζ.complexTest E.val.1 j‖ ^ 2) ≤
      (2 + 4 * d ^ 2 / (ω ^ 2 * m)) *
        (∑ j : Fin 3, ‖cutField hΩ χ H.val.1 j‖ ^ 2) := by
  have hlow : m * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => E.val.1 j x)) ≤
      ∫ x in Ω, ζ.function x ^ 2 * ε x * energy (fun j => E.val.1 j x) := by
    rw [← integral_const_mul]
    apply integral_mono_ae ((weighted_energy_integrable (squareTest ζ) E.val.1).const_mul m)
      (weighted_electric_integrable hΩ (squareTest ζ) ω hω ε E H hMax)
    filter_upwards [hε] with x hx
    dsimp [squareTest]
    nlinarith [mul_nonneg (sq_nonneg (ζ.function x)) (energy_nonneg (fun j => E.val.1 j x)),
      mul_nonneg (sub_nonneg.mpr hx)
        (mul_nonneg (sq_nonneg (ζ.function x)) (energy_nonneg (fun j => E.val.1 j x)))]
  have hc := caccioppoli hΩ ζ ω hω ε E H hMax m hm hε
  obtain ⟨hB, hG⟩ := cutoff_energy_support_bounds ζ H.val.1 hζ d hd
  have hs := unit_support_energy_le hΩ isClosed_closure.measurableSet χ hχ H.val.1
  have hcoef : 0 ≤ 4 / (ω ^ 2 * m) := by positivity
  rw [real_cutField_energy]
  calc
    _ ≤ _ := hlow.trans hc
    _ ≤ (2 + 4 * d ^ 2 / (ω ^ 2 * m)) *
        (∫ x in tsupport ζ.function, energy (fun j => H.val.1 j x)
          ∂DomainCurl.regionMeasure Ω) := by
      have h := add_le_add (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hG hcoef)
      convert h using 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

theorem electric_cutoff_norm_control {Ω : Set Space} (hΩ : IsOpen Ω)
    (ζ : RealTest Ω) (χ : DomainCurl.Test Ω)
    (hχ : ∀ x ∈ tsupport ζ.function, χ.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (d : ℝ)
    (hd : ∀ x, realEnergy (gradient ζ x) ≤ d ^ 2)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hMax : WeakMaxwell ω (fun _ => 1) ε E H) (m : ℝ) (hm : 0 < m)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, m ≤ ε x) :
    ‖cutField hΩ ζ.complexTest E.val.1‖ ≤
      Real.sqrt (3 * (2 + 4 * d ^ 2 / (ω ^ 2 * m)) / m) *
        ‖cutField hΩ χ H.val.1‖ := by
  have h := electric_cutoff_energy_control hΩ ζ χ hχ hζ d hd ω hω ε E H hMax m hm hε
  have he := (vector_energy_bounds (cutField hΩ ζ.complexTest E.val.1)).1
  have hh := (vector_energy_bounds (cutField hΩ χ H.val.1)).2
  let C := 2 + 4 * d ^ 2 / (ω ^ 2 * m)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsq : ‖cutField hΩ ζ.complexTest E.val.1‖ ^ 2 ≤
      (3 * C / m) * ‖cutField hΩ χ H.val.1‖ ^ 2 := by
    apply (mul_le_mul_left hm).mp
    have h1 := mul_le_mul_of_nonneg_left he hm.le
    have h2 := mul_le_mul_of_nonneg_left hh hC
    have heq : m * ((3 * C / m) * ‖cutField hΩ χ H.val.1‖ ^ 2) =
        C * (3 * ‖cutField hΩ χ H.val.1‖ ^ 2) := by field_simp; ring
    rw [heq]
    exact (h1.trans h).trans h2
  have hCs : 0 ≤ 3 * C / m := by positivity
  have hs := Real.sq_sqrt hCs
  have hn := Real.sqrt_nonneg (3 * C / m)
  change _ ≤ Real.sqrt (3 * C / m) * _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg _))).mp
  simpa only [mul_pow, hs] using hsq

end OQ14.ElectricControl

#print axioms OQ14.ElectricControl.regional_vector_norm_squared
#print axioms OQ14.ElectricControl.multiply_energy_ae
#print axioms OQ14.ElectricControl.cutField_energy
#print axioms OQ14.ElectricControl.real_cutField_energy
#print axioms OQ14.ElectricControl.unit_support_energy_le
#print axioms OQ14.ElectricControl.vector_energy_bounds
#print axioms OQ14.ElectricControl.electric_cutoff_energy_control
#print axioms OQ14.ElectricControl.electric_cutoff_norm_control

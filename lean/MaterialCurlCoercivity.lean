import MaxwellInverseCurlCurl
import WeakPoynting.MaterialCaccioppoli

/-! Coercivity of the actual dielectric magnetic curl energy on every subregion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaterialCurlCoercivity
open MeasureTheory OQ14.Maxwell
open OQ14.WeakConservation OQ14.WeakEnergy

theorem inverse_curl_energy_ae {Ω : Set Space} (k : ℝ) (ε : Space → ℝ)
    (hε : ∀ x, 0 < ε x) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell k (fun _ => 1) ε E H) :
    (fun x => (ε x)⁻¹ * energy (fun j => H.val.2 j x)) =ᵐ[DomainCurl.regionMeasure Ω]
      (fun x => k^2 * ε x * energy (fun j => E.val.1 j x)) := by
  filter_upwards [hM.2] with x hx
  have he : ε x ≠ 0 := (hε x).ne'
  simp only [energy, hx, map_mul, map_neg, Complex.normSq_neg, Complex.normSq_I,
    Complex.normSq_ofReal, one_mul]
  field_simp
  ring

theorem inverse_curl_caccioppoli {Ω : Set Space} (hΩ : IsOpen Ω) (ζ : RealTest Ω)
    (k : ℝ) (hk : k ≠ 0) (ε : Space → ℝ) (hε : ∀ x, 1 ≤ ε x)
    (E H : DomainCurl.HCurl Ω) (hM : WeakMaxwell k (fun _ => 1) ε E H) :
    (∫ x in Ω, ζ.function x^2 * (ε x)⁻¹ * energy (fun j => H.val.2 j x)) ≤
      2*k^2 * (∫ x in Ω, ζ.function x^2 * energy (fun j => H.val.1 j x)) +
        4 * (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => H.val.1 j x)) := by
  have hpos : ∀ x, 0 < ε x := fun x => lt_of_lt_of_le zero_lt_one (hε x)
  have henergy : (∫ x in Ω, ζ.function x^2 * (ε x)⁻¹ * energy (fun j => H.val.2 j x)) =
      k^2 * (∫ x in Ω, ζ.function x^2 * ε x * energy (fun j => E.val.1 j x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [inverse_curl_energy_ae k ε hpos E H hM] with x hx
    nlinarith
  rw [henergy]
  have hc := WeakEnergy.caccioppoli hΩ ζ k hk ε E H hM 1 zero_lt_one
    (Filter.Eventually.of_forall hε)
  have h := mul_le_mul_of_nonneg_left hc (sq_nonneg k)
  have hk2 : k^2 ≠ 0 := (sq_pos_of_ne_zero hk).ne'
  calc
    _ ≤ k^2 * (2 * (∫ x in Ω, ζ.function x ^ 2 * energy (fun j => H.val.1 j x)) +
      4 / (k^2 * 1) * (∫ x in Ω, realEnergy (gradient ζ x) * energy (fun j => H.val.1 j x))) := h
    _ = _ := by field_simp; ring

theorem curl_energy (c : StaticCoefficient.Coefficient) {Ω S : Set Space}
    (hS : S ⊆ Ω) (H : DomainCurl.HCurl Ω) (j : Fin 3) :
    (1+c.bound)⁻¹ * (∫ x in S, ‖H.val.2 j x‖^2) ≤
      ∫ x in S, (MaterialMaxwell.dielectric c x)⁻¹ * ‖H.val.2 j x‖^2 := by
  have hf : MemLp (fun x => H.val.2 j x) 2 (DomainCurl.regionMeasure S) :=
    (Lp.memLp (H.val.2 j)).mono_measure (Measure.restrict_mono hS le_rfl)
  apply MaxwellInverseCurlCurl.inverse_weight_coercivity (MaterialMaxwell.dielectric c) (1+c.bound)
    (MaterialHCurl.dielectric_measurable c)
  · intro x
    exact (MaterialMaxwell.dielectric_bounds c x).1
  · intro x
    exact (MaterialMaxwell.dielectric_bounds c x).2
  · exact hf

end OQ14.MaterialCurlCoercivity
#print axioms OQ14.MaterialCurlCoercivity.curl_energy
#print axioms OQ14.MaterialCurlCoercivity.inverse_curl_caccioppoli

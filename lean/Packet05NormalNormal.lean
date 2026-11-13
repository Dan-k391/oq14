import Packet05LocalDerivative

/-! Phasewise normal-normal recovery from the actual displacement relation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05NormalNormal
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05LocalDerivative

/-- If the normal displacement derivative equals minus ε times the
tangential divergence, its phasewise normal derivative is recovered from
the two already established mixed derivatives. -/
theorem phase_normal_normal_from_flux (V : Set Space) (d : ℝ) (hd : 0 ≤ d)
    (ε₀ : ℝ) (hε₀ : ε₀ ≠ 0)
    (hε : ∀ x ∈ V, FlatDifferenceCoercivity.dielectric d x = ε₀)
    (u N A0 A1 P0 P1 : L2Scalar) (τ : Test)
    (hτ : ∀ x ∈ V, τ.function x = 1)
    (hN : HasWeakPartial (Packet05FlatWeight.mulWeight d hd u) N 2)
    (hflux : ∀ᵐ x ∂volume, x ∈ V →
      N x = -(Packet05FlatWeight.weight d x) * (A0 x + A1 x))
    (hP0 : HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact A0) P0 2)
    (hP1 : HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact A1) P1 2) :
    (∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ (((ε₀ : ℂ)⁻¹) • N) + derivativePair φ 2 u = 0) ∧
    (∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ (-(P0+P1)) + derivativePair φ 2 (((ε₀ : ℂ)⁻¹) • N) = 0) := by
  refine ⟨weighted_partial_gives_phase_partial V d hd ε₀ hε₀ hε u N 2 hN, ?_⟩
  have hp : HasWeakPartial
      (-(scaleL2 τ.function τ.regular.continuous τ.compact A0 +
        scaleL2 τ.function τ.regular.continuous τ.compact A1)) (-(P0+P1)) 2 := by
    intro φ
    have h0 := hP0 φ
    have h1 := hP1 φ
    simp only [map_neg, map_add]
    linear_combination -h0-h1
  apply local_partial_of_ae_eq V (((ε₀ : ℂ)⁻¹) • N)
    (-(scaleL2 τ.function τ.regular.continuous τ.compact A0 +
      scaleL2 τ.function τ.regular.continuous τ.compact A1)) (-(P0+P1)) 2 hp
  have hn : (ε₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε₀
  filter_upwards [hflux, Lp.coeFn_smul ((ε₀ : ℂ)⁻¹) N,
    Lp.coeFn_neg (scaleL2 τ.function τ.regular.continuous τ.compact A0 +
      scaleL2 τ.function τ.regular.continuous τ.compact A1),
    Lp.coeFn_add (scaleL2 τ.function τ.regular.continuous τ.compact A0)
      (scaleL2 τ.function τ.regular.continuous τ.compact A1),
    scaleL2_ae τ.function τ.regular.continuous τ.compact A0,
    scaleL2_ae τ.function τ.regular.continuous τ.compact A1] with x hf hs hn' ha h0 h1 hx
  rw [hs, hn']
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hf hx, h0, h1, hτ x hx]
  simp only [Packet05FlatWeight.weight, hε x hx, Complex.ofReal_neg, one_mul]
  field_simp
  ring

/-- On a region, a curl equation gives the normal derivative of E₀ from
the tangential derivative of E₂ and the corresponding magnetic component. -/
theorem normal_first_component_from_local_curl (V : Set Space) (E C H : L2Vector)
    (a : ℂ) (D : L2Scalar) (hcurl : HasWeakCurl E C)
    (hD : HasWeakPartial (E 2) D 0)
    (hC : ∀ᵐ x ∂volume, x ∈ V → C 1 x = a * H 1 x) :
    ∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ D + a * valuePair φ (H 1) + derivativePair φ 2 (E 0) = 0 := by
  intro φ hφV
  have he : valuePair φ (C 1) = a * valuePair φ (H 1) := by
    simp only [valuePair, testPair_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hC] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV]
      ring
    · have hz : φ.function x = 0 := image_eq_zero_of_nmem_tsupport (fun hx => hxV (hφV hx))
      simp [hz]
  have hc := hcurl φ 1
  have hd := hD φ
  change derivativePair φ 0 (E 2) - derivativePair φ 2 (E 0) - valuePair φ (C 1) = 0 at hc
  rw [he] at hc
  linear_combination -hc + hd

/-- The analogous normal derivative identity for E₁. -/
theorem normal_second_component_from_local_curl (V : Set Space) (E C H : L2Vector)
    (a : ℂ) (D : L2Scalar) (hcurl : HasWeakCurl E C)
    (hD : HasWeakPartial (E 2) D 1)
    (hC : ∀ᵐ x ∂volume, x ∈ V → C 0 x = a * H 0 x) :
    ∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ D - a * valuePair φ (H 0) + derivativePair φ 2 (E 1) = 0 := by
  intro φ hφV
  have he : valuePair φ (C 0) = a * valuePair φ (H 0) := by
    simp only [valuePair, testPair_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hC] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV]
      ring
    · have hz : φ.function x = 0 := image_eq_zero_of_nmem_tsupport (fun hx => hxV (hφV hx))
      simp [hz]
  have hc := hcurl φ 0
  have hd := hD φ
  change derivativePair φ 2 (E 1) - derivativePair φ 1 (E 2) - valuePair φ (C 0) = 0 at hc
  rw [he] at hc
  linear_combination hc + hd

theorem valuePair_cutoff_on (V : Set Space) (τ φ : Test) (u : L2Scalar)
    (hτ : ∀ x ∈ V, τ.function x = 1) (hφ : tsupport φ.function ⊆ V) :
    valuePair φ (scaleL2 τ.function τ.regular.continuous τ.compact u) = valuePair φ u := by
  simp only [valuePair, testPair_integral]
  apply integral_congr_ae
  filter_upwards [scaleL2_ae τ.function τ.regular.continuous τ.compact u] with x hx
  rw [hx]
  by_cases hxV : x ∈ V
  · simp [hτ x hxV]
  · have hz : φ.function x = 0 := image_eq_zero_of_nmem_tsupport (fun hx => hxV (hφ hx))
    simp [hz]

/-- Complete a phasewise normal-normal derivative of a tangential component
from its local first-normal formula, the mixed derivative and magnetic H1. -/
theorem phase_tangential_normal_normal (V : Set Space) (E D H G QH : L2Scalar)
    (a : ℂ) (τ : Test) (hτ : ∀ x ∈ V, τ.function x = 1)
    (hfirst : ∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ D + a * valuePair φ H + derivativePair φ 2 E = 0)
    (hmixed : ∀ φ : Test, tsupport φ.function ⊆ V →
      valuePair φ G + derivativePair φ 2
        (scaleL2 τ.function τ.regular.continuous τ.compact D) = 0)
    (hmag : HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact H) QH 2) :
    ∃ N Q : L2Scalar,
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ N + derivativePair φ 2 E = 0) ∧
      (∀ φ : Test, tsupport φ.function ⊆ V → valuePair φ Q + derivativePair φ 2 N = 0) := by
  refine ⟨scaleL2 τ.function τ.regular.continuous τ.compact D +
      a • scaleL2 τ.function τ.regular.continuous τ.compact H,
    G + a • QH, ?_, ?_⟩
  · intro φ hφ
    simp only [map_add, map_smul, smul_eq_mul]
    rw [valuePair_cutoff_on V τ φ D hτ hφ, valuePair_cutoff_on V τ φ H hτ hφ]
    exact hfirst φ hφ
  · intro φ hφ
    have h1 := hmixed φ hφ
    have h2 := hmag φ
    simp only [map_add, map_smul, smul_eq_mul]
    linear_combination h1 + a*h2

end OQ14.Packet05NormalNormal
#print axioms OQ14.Packet05NormalNormal.phase_normal_normal_from_flux
#print axioms OQ14.Packet05NormalNormal.normal_first_component_from_local_curl
#print axioms OQ14.Packet05NormalNormal.normal_second_component_from_local_curl
#print axioms OQ14.Packet05NormalNormal.valuePair_cutoff_on
#print axioms OQ14.Packet05NormalNormal.phase_tangential_normal_normal

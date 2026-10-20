import RadialIntervalUniqueness
import RadialMomentODE

/-! # Actual finite-interval moment and flux uniqueness -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialIntervalFlux

open Complex Filter Set OQ14.RadialMomentODE OQ14.RadialIntervalUniqueness
open scoped Topology

theorem flux_state_zero_of_riccati_zero (U F : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hu : riccati U r = 0) (hf : riccatiD U F r = 0) : U r = 0 ∧ F r = 0 := by
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hU : U r = 0 := (mul_eq_zero.mp hu).resolve_left hrc
  have hF : F r/(r : ℂ) = 0 := by simpa only [riccatiD,hU,zero_add] using hf
  exact ⟨hU,(div_eq_zero_iff.mp hF).resolve_right hrc⟩

theorem flux_zero_on_interval (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (U F : ℝ → ℂ)
    (hU : ∀ r ∈ Ioo R L, HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r ∈ Ioo R L, HasDerivAt F
      (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*U r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (hU₀ : U r₀ = 0) (hF₀ : F r₀ = 0) :
    ∀ r ∈ Ioo R L, U r = 0 ∧ F r = 0 := by
  have hn (r : ℝ) (hr : r ∈ Ioo R L) : r ≠ 0 := ne_of_gt (lt_of_le_of_lt hR hr.1)
  have hz := radial_ode_zero_on_interval l k hk R L hR (riccati U) (riccatiD U F)
    (fun r hr => riccati_hasDerivAt U F r (hn r hr) (hU r hr))
    (fun r hr => riccatiD_hasDerivAt l k U F r (hn r hr) (hU r hr) (hF r hr))
    r₀ hr₀ (by simp [riccati,hU₀]) (by simp [riccatiD,hU₀,hF₀])
  intro r hr
  exact flux_state_zero_of_riccati_zero U F r (hn r hr) (hz r hr).1 (hz r hr).2

theorem flux_zero_of_zero_neighborhood (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (U F : ℝ → ℂ)
    (hU : ∀ r ∈ Ioo R L, HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r ∈ Ioo R L, HasDerivAt F
      (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*U r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (hzero : U =ᶠ[𝓝 r₀] 0) :
    ∀ r ∈ Ioo R L, U r = 0 ∧ F r = 0 := by
  have hn (r : ℝ) (hr : r ∈ Ioo R L) : r ≠ 0 := ne_of_gt (lt_of_le_of_lt hR hr.1)
  have hric : riccati U =ᶠ[𝓝 r₀] 0 := by
    filter_upwards [hzero] with r hr
    simp only [riccati,hr,mul_zero,Pi.zero_apply]
  have hz := radial_ode_zero_of_zero_neighborhood l k hk R L hR (riccati U) (riccatiD U F)
    (fun r hr => riccati_hasDerivAt U F r (hn r hr) (hU r hr))
    (fun r hr => riccatiD_hasDerivAt l k U F r (hn r hr) (hU r hr) (hF r hr)) r₀ hr₀ hric
  intro r hr
  exact flux_state_zero_of_riccati_zero U F r (hn r hr) (hz r hr).1 (hz r hr).2

theorem flux_solutions_unique_on_interval (l : ℕ) (k : ℂ) (hk : k ≠ 0)
    (R L : ℝ) (hR : 0 ≤ R) (U F V G : ℝ → ℂ)
    (hU : ∀ r ∈ Ioo R L, HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r ∈ Ioo R L, HasDerivAt F
      (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*U r) r)
    (hV : ∀ r ∈ Ioo R L, HasDerivAt V (G r/(r : ℂ)^2) r)
    (hG : ∀ r ∈ Ioo R L, HasDerivAt G
      (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*V r) r)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo R L) (hU₀ : U r₀ = V r₀) (hF₀ : F r₀ = G r₀) :
    ∀ r ∈ Ioo R L, U r = V r ∧ F r = G r := by
  have hz := flux_zero_on_interval l k hk R L hR (fun r => U r-V r) (fun r => F r-G r)
    (fun r hr => by simpa only [sub_div] using (hU r hr).sub (hV r hr))
    (fun r hr => by simpa only [mul_sub] using (hF r hr).sub (hG r hr))
    r₀ hr₀ (sub_eq_zero.mpr hU₀) (sub_eq_zero.mpr hF₀)
  intro r hr
  exact ⟨sub_eq_zero.mp (hz r hr).1,sub_eq_zero.mp (hz r hr).2⟩

end OQ14.RadialIntervalFlux

#print axioms OQ14.RadialIntervalFlux.flux_state_zero_of_riccati_zero
#print axioms OQ14.RadialIntervalFlux.flux_zero_on_interval
#print axioms OQ14.RadialIntervalFlux.flux_zero_of_zero_neighborhood
#print axioms OQ14.RadialIntervalFlux.flux_solutions_unique_on_interval
